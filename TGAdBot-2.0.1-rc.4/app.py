import os, json, time, sqlite3, threading, secrets, logging, hmac, uuid, mimetypes, hashlib, re, base64, math
from datetime import datetime, timezone, timedelta
from functools import wraps
from contextlib import contextmanager, nullcontext
from urllib.parse import urlparse

import requests
import delivery_v2
import material_library
import button_actions
from cryptography.fernet import Fernet, InvalidToken
from markupsafe import Markup
from flask import Flask, request, redirect, url_for, flash, render_template_string, session, abort, jsonify
from flask_wtf.csrf import CSRFProtect
try:
    from werkzeug.middleware.proxy_fix import ProxyFix
except ImportError:  # Test shim / minimal import environments.
    ProxyFix = None

APP_SECRET = os.getenv("APP_SECRET", "")
DB_PATH = os.getenv("DB_PATH", "tgadbot.sqlite3")
MEDIA_DIR = os.getenv("MEDIA_DIR", os.path.join(os.path.dirname(DB_PATH) or ".", "media"))
POLLING_ENABLED = os.getenv("POLLING_ENABLED", "1") == "1"
POLL_TIMEOUT = int(os.getenv("POLL_TIMEOUT", "25"))
SEND_GAP_SECONDS = max(10.0, min(3600.0, float(os.getenv("SEND_GAP_SECONDS", "10"))))
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD", "")
ENCRYPTION_KEY = os.getenv("ENCRYPTION_KEY", "")
TELEGRAM_LOGIN_BOT_TOKEN = os.getenv("TELEGRAM_LOGIN_BOT_TOKEN", "")
TELEGRAM_LOGIN_BOT_USERNAME = os.getenv("TELEGRAM_LOGIN_BOT_USERNAME", "").lstrip("@")
TELEGRAM_LOGIN_ALLOWED_USER_IDS = {x.strip() for x in os.getenv("TELEGRAM_LOGIN_ALLOWED_USER_IDS", "").split(",") if x.strip()}
TELEGRAM_LOGIN_ADMIN_USER_IDS = {x.strip() for x in os.getenv("TELEGRAM_LOGIN_ADMIN_USER_IDS", "").split(",") if x.strip()}
ALLOW_PUBLIC_REGISTRATION = os.getenv("ALLOW_PUBLIC_REGISTRATION", "1") == "1"
APP_VERSION = "2.0.1-rc.3"
FORCED_AD_MODE = "BOTH"  # Default platform-ad policy; administrators can change its mode.
LOG_RETENTION_HOURS = max(1, int(os.getenv("LOG_RETENTION_HOURS", "12")))
LOG_CLEANUP_INTERVAL_SECONDS = max(300, int(os.getenv("LOG_CLEANUP_INTERVAL_SECONDS", "3600")))
DEFAULT_TASK_SEND_GAP_SECONDS = 10.0
MIN_TASK_SEND_GAP_SECONDS = 10.0
MAX_TASK_SEND_GAP_SECONDS = 3600.0

app = Flask(__name__)
if ProxyFix is not None and hasattr(app, "wsgi_app"):
    # Production is bound to localhost behind Nginx; honor its forwarded HTTPS host/scheme.
    app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)
app.secret_key = APP_SECRET
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.getenv("SESSION_COOKIE_SECURE", "1") == "1",
    PERMANENT_SESSION_LIFETIME=timedelta(hours=8),
    WTF_CSRF_TIME_LIMIT=7200,
    MAX_CONTENT_LENGTH=52 * 1024 * 1024,
)
csrf = CSRFProtect(app)
cipher = None

def validate_config():
    missing = [name for name, value in (
        ("APP_SECRET", APP_SECRET),
        ("ADMIN_PASSWORD", ADMIN_PASSWORD),
        ("ENCRYPTION_KEY", ENCRYPTION_KEY),
    ) if not value]
    if missing:
        raise RuntimeError("缺少必需环境变量：" + ", ".join(missing))
    if len(APP_SECRET) < 32:
        raise RuntimeError("APP_SECRET 至少需要 32 个字符")
    if len(ADMIN_PASSWORD) < 12:
        raise RuntimeError("ADMIN_PASSWORD 至少需要 12 个字符")
    try:
        Fernet(ENCRYPTION_KEY.encode("ascii"))
    except Exception as exc:
        raise RuntimeError("ENCRYPTION_KEY 必须是有效的 Fernet key") from exc

def login_required(fn):
    @wraps(fn)
    def wrapped(*args, **kwargs):
        if not session.get("authenticated"):
            return redirect(url_for("login", next=request.path))
        if session.get("auth_method") != "admin_password":
            user_id = str(session.get("user_id") or session.get("telegram_user_id") or "")
            with db() as c:
                user = c.execute("SELECT status FROM user_accounts WHERE id=?", (user_id,)).fetchone() if user_id else None
            if not user or user["status"] != "active":
                session.clear()
                flash("账号不存在或已被平台停用，请重新登录或联系管理员。")
                return redirect(url_for("login"))
        return fn(*args, **kwargs)
    return wrapped


def is_admin_user():
    if session.get("auth_method") == "admin_password" and session.get("is_admin"):
        return True
    user_id = str(session.get("user_id") or session.get("telegram_user_id") or "")
    if not user_id:
        return False
    with db() as c:
        user = c.execute("SELECT role,status FROM user_accounts WHERE id=?", (user_id,)).fetchone()
    return bool(user and user["status"] == "active" and user["role"] == "admin")


def current_owner_id():
    # Existing pre-multi-user data remains owned by the legacy administrator.
    if session.get("auth_method") == "admin_password":
        return "legacy_admin"
    return str(session.get("user_id") or session.get("telegram_user_id") or "legacy_admin")


def owner_clause(column="owner_user_id"):
    if is_admin_user():
        return "1=1", []
    return f"{column}=?", [current_owner_id()]


def require_admin():
    if not is_admin_user():
        abort(403)


def forced_ad_mode():
    value = setting("forced_ad_mode") or FORCED_AD_MODE
    return value if value in ("TEXT_ONLY", "BUTTON_ONLY", "BOTH") else FORCED_AD_MODE

def encrypt_token(token):
    if cipher is None:
        raise RuntimeError("Token 加密尚未初始化")
    return cipher.encrypt(token.encode("utf-8")).decode("ascii")

def decrypt_token(value):
    if cipher is None:
        raise RuntimeError("Token 加密尚未初始化")
    try:
        return cipher.decrypt(value.encode("ascii")).decode("utf-8")
    except (InvalidToken, UnicodeError, ValueError) as exc:
        raise RuntimeError("Bot Token 解密失败；请检查 ENCRYPTION_KEY 是否与原部署一致") from exc


def verify_telegram_login(data, bot_token=None, max_age_seconds=300, now_ts=None):
    token = bot_token if bot_token is not None else TELEGRAM_LOGIN_BOT_TOKEN
    if not token:
        return False, "Telegram 登录尚未配置"
    supplied_hash = str(data.get("hash") or "")
    auth_date = str(data.get("auth_date") or "")
    if not supplied_hash or not auth_date:
        return False, "Telegram 登录数据缺少签名或时间"
    try:
        auth_ts = int(auth_date)
    except ValueError:
        return False, "Telegram 登录时间无效"
    current = int(time.time()) if now_ts is None else int(now_ts)
    if auth_ts > current + 60 or current - auth_ts > int(max_age_seconds):
        return False, "Telegram 登录凭证已过期或时间异常"
    fields = []
    for key in sorted(data):
        if key == "hash":
            continue
        value = data[key]
        if isinstance(value, (str, int, float)):
            fields.append(f"{key}={value}")
    check_string = "\n".join(fields)
    secret_key = hashlib.sha256(token.encode("utf-8")).digest()
    expected = hmac.new(secret_key, check_string.encode("utf-8"), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, supplied_hash):
        return False, "Telegram 登录签名验证失败"
    user_id = str(data.get("id") or "")
    if not user_id:
        return False, "Telegram 用户 ID 缺失"
    # Empty allowlist allows Telegram-widget login; a non-empty list restricts
    # only Telegram-widget login and does not grant platform-admin permissions.
    if TELEGRAM_LOGIN_ALLOWED_USER_IDS and user_id not in TELEGRAM_LOGIN_ALLOWED_USER_IDS:
        return False, "该 Telegram 用户没有登录权限"
    return True, user_id


def consume_telegram_login_hash(signed_hash, now_ts=None):
    """Atomically consume a signed Telegram Login Widget hash exactly once."""
    value = str(signed_hash or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", value):
        return False
    current = int(time.time()) if now_ts is None else int(now_ts)
    with db() as c:
        # Keep a consumed hash for 24 hours after use, longer than the accepted
        # 5-minute auth_date window, so concurrent/replayed callbacks are rejected.
        c.execute("DELETE FROM telegram_login_uses WHERE consumed_at < ?", (current - 86400,))
        cur = c.execute(
            "INSERT OR IGNORE INTO telegram_login_uses(login_hash, consumed_at) VALUES(?,?)",
            (value, current),
        )
        return cur.rowcount == 1


def parse_rotation_messages(rotation_raw):
    """Parse the UI's explicit separator into ordered non-empty message variants."""
    if not rotation_raw:
        return []
    return [item.strip() for item in re.split(r"\n\s*---轮换消息---\s*\n", rotation_raw) if item.strip()]


def parse_send_gap_seconds(preset, custom_value=""):
    """Validate a per-task delay between consecutive group delivery jobs."""
    raw = custom_value if str(preset) == "custom" else preset
    min_gap = platform_send_gap_seconds()
    if str(preset) != "custom" and (raw is None or str(raw).strip() == ""):
        return round(min_gap, 1)
    try:
        value = float(raw)
    except (TypeError, ValueError) as exc:
        raise ValueError("请输入有效的群组发送间隔秒数") from exc
    if not math.isfinite(value) or value < min_gap or value > MAX_TASK_SEND_GAP_SECONDS:
        raise ValueError(f"群组发送间隔不能低于平台最低间隔 {min_gap:g} 秒（范围 {min_gap:g} 至 {MAX_TASK_SEND_GAP_SECONDS:g} 秒）")
    return round(value, 1)


def login_is_rate_limited(ip):
    cutoff = int(time.time()) - 600
    with db() as c:
        row = c.execute("SELECT COUNT(*) AS n FROM login_attempts WHERE ip=? AND attempted_at>=?", (ip, cutoff)).fetchone()
    return row["n"] >= 5

def record_login_failure(ip):
    current = int(time.time())
    with db() as c:
        c.execute("DELETE FROM login_attempts WHERE attempted_at<?", (current - 86400,))
        c.execute("INSERT INTO login_attempts(ip, attempted_at) VALUES(?,?)", (ip, current))

def clear_login_failures(ip):
    with db() as c:
        c.execute("DELETE FROM login_attempts WHERE ip=?", (ip,))


def hash_password(password):
    """PBKDF2-SHA256 password hash using only Python's standard library."""
    salt = secrets.token_bytes(16)
    iterations = 310000
    digest = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, iterations)
    return "pbkdf2_sha256${}${}${}".format(
        iterations,
        base64.urlsafe_b64encode(salt).decode("ascii"),
        base64.urlsafe_b64encode(digest).decode("ascii"),
    )


def verify_password(password, encoded):
    try:
        algorithm, iterations, salt_text, digest_text = encoded.split("$", 3)
        if algorithm != "pbkdf2_sha256":
            return False
        salt = base64.urlsafe_b64decode(salt_text.encode("ascii"))
        expected = base64.urlsafe_b64decode(digest_text.encode("ascii"))
        actual = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, int(iterations))
        return hmac.compare_digest(actual, expected)
    except (ValueError, TypeError, UnicodeError):
        return False


def registration_is_rate_limited(ip):
    cutoff = int(time.time()) - 3600
    with db() as c:
        row = c.execute("SELECT COUNT(*) AS n FROM registration_attempts WHERE ip=? AND attempted_at>=?", (ip, cutoff)).fetchone()
    return row["n"] >= 10


def record_registration_attempt(ip):
    current = int(time.time())
    with db() as c:
        c.execute("DELETE FROM registration_attempts WHERE attempted_at<?", (current - 86400,))
        c.execute("INSERT INTO registration_attempts(ip,attempted_at) VALUES(?,?)", (ip, current))


def create_local_user(email, password, username=""):
    email = str(email or "").strip().lower()
    username = str(username or "").strip()[:64]
    if not email or len(email) > 254 or not re.fullmatch(r"[^\s@]+@[^\s@]+\.[^\s@]+", email):
        raise ValueError("请输入有效邮箱地址（最多 254 个字符）。")
    if len(password or "") < 6:
        raise ValueError("密码至少需要 6 个字符。")
    if len(password) > 1024:
        raise ValueError("密码长度不能超过 1024 个字符。")
    user_id = "local:" + uuid.uuid4().hex
    timestamp = now()
    with db() as c:
        c.execute("""INSERT INTO user_accounts(id,email,password_hash,username,role,status,created_at,last_login_at)
            VALUES(?,?,?,?, 'user','active',?,?)""",
            (user_id,email,hash_password(password),username or email.split("@",1)[0],timestamp,timestamp))
    return user_id


def authenticate_local_user(email, password):
    email = str(email or "").strip().lower()
    with db() as c:
        user = c.execute("SELECT * FROM user_accounts WHERE lower(email)=lower(?)", (email,)).fetchone()
    if not user or user["status"] != "active" or not user["password_hash"]:
        return None
    return user if verify_password(password or "", user["password_hash"]) else None
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
polling_threads = {}
stop_events = {}
polling_lock = threading.Lock()

@contextmanager
def db():
    con = sqlite3.connect(DB_PATH, timeout=30)
    con.row_factory = sqlite3.Row
    try:
        yield con
        con.commit()
    except Exception:
        con.rollback()
        raise
    finally:
        con.close()

def init_db():
    global cipher
    validate_config()
    from migrations import backup_before_upgrade
    backup_before_upgrade(DB_PATH)
    cipher = Fernet(ENCRYPTION_KEY.encode("ascii"))
    with db() as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS announcements(
          id INTEGER PRIMARY KEY AUTOINCREMENT,title TEXT NOT NULL,body TEXT NOT NULL,
          enabled INTEGER NOT NULL DEFAULT 1,pinned INTEGER NOT NULL DEFAULT 0,published_at INTEGER NOT NULL);
        CREATE TABLE IF NOT EXISTS log_visibility(
          owner_user_id TEXT PRIMARY KEY, hidden_before TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS bots(
          id INTEGER PRIMARY KEY AUTOINCREMENT, token TEXT NOT NULL UNIQUE,
          telegram_id INTEGER NOT NULL, username TEXT, first_name TEXT,
          token_encryption_version INTEGER NOT NULL DEFAULT 0,
          status TEXT NOT NULL DEFAULT 'active', offset INTEGER NOT NULL DEFAULT 0,
          last_api_status TEXT NOT NULL DEFAULT 'pending', last_api_error TEXT, last_api_ok_at TEXT,
          created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS chats(
          id INTEGER PRIMARY KEY AUTOINCREMENT, bot_id INTEGER NOT NULL,
          chat_id INTEGER NOT NULL, title TEXT, chat_type TEXT,
          status TEXT NOT NULL DEFAULT 'active', last_seen TEXT,
          UNIQUE(bot_id, chat_id)
        );
        CREATE TABLE IF NOT EXISTS settings(
          key TEXT PRIMARY KEY, value TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS users(
          telegram_user_id TEXT PRIMARY KEY,
          username TEXT, first_name TEXT, last_name TEXT,
          created_at TEXT NOT NULL, last_login_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS user_accounts(
          id TEXT PRIMARY KEY,
          telegram_user_id TEXT UNIQUE,
          email TEXT,
          password_hash TEXT,
          username TEXT, first_name TEXT, last_name TEXT,
          role TEXT NOT NULL DEFAULT 'user',
          status TEXT NOT NULL DEFAULT 'active',
          created_at TEXT NOT NULL, last_login_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS media_assets(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          bot_id INTEGER NOT NULL,
          source_chat_id INTEGER,
          source_chat_title TEXT,
          source_message_id INTEGER,
          media_type TEXT NOT NULL CHECK(media_type IN ('photo','video')),
          file_id TEXT NOT NULL,
          file_unique_id TEXT,
          caption TEXT,
          file_size INTEGER,
          media_group_id TEXT,
          source_message_json TEXT,
          created_at TEXT NOT NULL,
          UNIQUE(bot_id,file_unique_id)
        );
        CREATE INDEX IF NOT EXISTS idx_media_assets_bot_type ON media_assets(bot_id,media_type,id DESC);
        CREATE TABLE IF NOT EXISTS login_attempts(ip TEXT NOT NULL, attempted_at INTEGER NOT NULL);
        CREATE INDEX IF NOT EXISTS idx_login_attempts_ip_time ON login_attempts(ip, attempted_at);
        CREATE TABLE IF NOT EXISTS registration_attempts(ip TEXT NOT NULL, attempted_at INTEGER NOT NULL);
        CREATE INDEX IF NOT EXISTS idx_registration_attempts_ip_time ON registration_attempts(ip, attempted_at);
        CREATE TABLE IF NOT EXISTS tasks(
          id INTEGER PRIMARY KEY AUTOINCREMENT, bot_ids TEXT NOT NULL,
          chat_targets TEXT NOT NULL, body TEXT NOT NULL, buttons TEXT NOT NULL,
          ad_mode TEXT NOT NULL, ad_text TEXT NOT NULL, ad_button_text TEXT NOT NULL,
          ad_url TEXT NOT NULL, status TEXT NOT NULL, created_at TEXT NOT NULL,
          result TEXT, media_path TEXT, media_type TEXT, scheduled_at INTEGER, rotation_messages TEXT, series_id INTEGER,
          send_gap_seconds REAL NOT NULL DEFAULT 10.0,
          sender_mode TEXT NOT NULL DEFAULT 'hide'
        );
        CREATE TABLE IF NOT EXISTS delivery_jobs(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          task_id INTEGER NOT NULL,
          bot_id INTEGER NOT NULL,
          chat_id INTEGER NOT NULL,
          chat_title TEXT NOT NULL,
          sequence_no INTEGER NOT NULL DEFAULT 0,
          rotation_index INTEGER NOT NULL DEFAULT 0,
          status TEXT NOT NULL DEFAULT 'pending',
          attempts INTEGER NOT NULL DEFAULT 0,
          next_attempt_at INTEGER NOT NULL DEFAULT 0,
          last_error TEXT,
          created_at TEXT NOT NULL,
          updated_at TEXT NOT NULL,
          UNIQUE(task_id, bot_id, chat_id),
          FOREIGN KEY(task_id) REFERENCES tasks(id)
        );
        CREATE INDEX IF NOT EXISTS idx_delivery_jobs_ready ON delivery_jobs(status, next_attempt_at, id);
        CREATE TABLE IF NOT EXISTS join_auto_sends(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          bot_id INTEGER NOT NULL,
          chat_id INTEGER NOT NULL,
          chat_title TEXT NOT NULL,
          status TEXT NOT NULL DEFAULT 'pending',
          next_attempt_at INTEGER NOT NULL,
          attempts INTEGER NOT NULL DEFAULT 0,
          last_error TEXT,
          created_at TEXT NOT NULL,
          updated_at TEXT NOT NULL,
          UNIQUE(bot_id,chat_id)
        );
        CREATE INDEX IF NOT EXISTS idx_join_auto_ready ON join_auto_sends(status,next_attempt_at,id);
        CREATE TABLE IF NOT EXISTS task_join_auto_sends(
          id INTEGER PRIMARY KEY AUTOINCREMENT,
          task_id INTEGER NOT NULL, bot_id INTEGER NOT NULL,
          chat_id INTEGER NOT NULL, chat_title TEXT NOT NULL,
          status TEXT NOT NULL DEFAULT 'pending', next_attempt_at INTEGER NOT NULL,
          attempts INTEGER NOT NULL DEFAULT 0, rotation_index INTEGER NOT NULL DEFAULT 0,
          last_error TEXT, created_at TEXT NOT NULL, updated_at TEXT NOT NULL,
          UNIQUE(task_id,bot_id,chat_id)
        );
        CREATE INDEX IF NOT EXISTS idx_task_join_auto_ready ON task_join_auto_sends(status,next_attempt_at,id);
        CREATE TABLE IF NOT EXISTS recurring_series(
          id INTEGER PRIMARY KEY AUTOINCREMENT, config_json TEXT NOT NULL,
          interval_seconds INTEGER NOT NULL DEFAULT 0, max_runs INTEGER NOT NULL DEFAULT 0,
          runs_created INTEGER NOT NULL DEFAULT 1, next_run_at INTEGER NOT NULL,
          last_task_id INTEGER, status TEXT NOT NULL DEFAULT 'active',
          created_at TEXT NOT NULL, updated_at TEXT NOT NULL,
          loop_mode TEXT NOT NULL DEFAULT 'legacy_interval',
          stop_after_seconds INTEGER NOT NULL DEFAULT 0,
          started_at INTEGER, ends_at INTEGER, paused_at INTEGER
        );
        CREATE INDEX IF NOT EXISTS idx_recurring_ready ON recurring_series(status,next_run_at,id);
        CREATE TABLE IF NOT EXISTS task_templates(
          id INTEGER PRIMARY KEY AUTOINCREMENT, title TEXT NOT NULL,
          config_json TEXT NOT NULL, created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS telegram_login_uses(
          login_hash TEXT PRIMARY KEY,
          consumed_at INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_telegram_login_uses_consumed
          ON telegram_login_uses(consumed_at);
        """)
        c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_user_accounts_telegram_id ON user_accounts(telegram_user_id) WHERE telegram_user_id IS NOT NULL")
        c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_user_accounts_email_unique ON user_accounts(lower(email)) WHERE email IS NOT NULL AND email<>''")
        # Additive backfill: old Telegram identity rows remain in their original table
        # so rollback to v1.1.0 can still read/write the legacy schema.
        c.execute("""INSERT OR IGNORE INTO user_accounts(id,telegram_user_id,username,first_name,last_name,role,status,created_at,last_login_at)
            SELECT telegram_user_id,telegram_user_id,username,first_name,last_name,'user','active',created_at,last_login_at FROM users""")
        delivery_columns = {row["name"] for row in c.execute("PRAGMA table_info(delivery_jobs)").fetchall()}
        if "sequence_no" not in delivery_columns:
            c.execute("ALTER TABLE delivery_jobs ADD COLUMN sequence_no INTEGER NOT NULL DEFAULT 0")
        if "rotation_index" not in delivery_columns:
            c.execute("ALTER TABLE delivery_jobs ADD COLUMN rotation_index INTEGER NOT NULL DEFAULT 0")
        task_columns = {row["name"] for row in c.execute("PRAGMA table_info(tasks)").fetchall()}
        if "media_path" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN media_path TEXT")
        if "media_type" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN media_type TEXT")
        if "scheduled_at" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN scheduled_at INTEGER")
        if "rotation_messages" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN rotation_messages TEXT NOT NULL DEFAULT '[]'")
        if "series_id" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN series_id INTEGER")
        if "content_modes" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN content_modes TEXT NOT NULL DEFAULT '[\"text\"]'")
        if "media_assets" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN media_assets TEXT NOT NULL DEFAULT '{}' ")
        if "auto_join_enabled" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN auto_join_enabled INTEGER NOT NULL DEFAULT 0")
        if "owner_user_id" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN owner_user_id TEXT NOT NULL DEFAULT 'legacy_admin'")
        if "send_gap_seconds" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN send_gap_seconds REAL NOT NULL DEFAULT 10.0")
        if "sender_mode" not in task_columns:
            c.execute("ALTER TABLE tasks ADD COLUMN sender_mode TEXT NOT NULL DEFAULT 'hide'")
        c.execute("UPDATE tasks SET send_gap_seconds=? WHERE send_gap_seconds IS NULL OR send_gap_seconds<?",
                  (MIN_TASK_SEND_GAP_SECONDS, MIN_TASK_SEND_GAP_SECONDS))
        task_join_columns = {row["name"] for row in c.execute("PRAGMA table_info(task_join_auto_sends)").fetchall()}
        if "rotation_index" not in task_join_columns:
            c.execute("ALTER TABLE task_join_auto_sends ADD COLUMN rotation_index INTEGER NOT NULL DEFAULT 0")
        media_columns = {row["name"] for row in c.execute("PRAGMA table_info(media_assets)").fetchall()}
        if "media_group_id" not in media_columns:
            c.execute("ALTER TABLE media_assets ADD COLUMN media_group_id TEXT")
        if "source_message_json" not in media_columns:
            c.execute("ALTER TABLE media_assets ADD COLUMN source_message_json TEXT")
        columns = {row["name"] for row in c.execute("PRAGMA table_info(bots)").fetchall()}
        if "token_encryption_version" not in columns:
            c.execute("ALTER TABLE bots ADD COLUMN token_encryption_version INTEGER NOT NULL DEFAULT 0")
        if "last_api_status" not in columns:
            c.execute("ALTER TABLE bots ADD COLUMN last_api_status TEXT NOT NULL DEFAULT 'pending'")
        if "last_api_error" not in columns:
            c.execute("ALTER TABLE bots ADD COLUMN last_api_error TEXT")
        if "last_api_ok_at" not in columns:
            c.execute("ALTER TABLE bots ADD COLUMN last_api_ok_at TEXT")
        if "owner_user_id" not in columns:
            c.execute("ALTER TABLE bots ADD COLUMN owner_user_id TEXT NOT NULL DEFAULT 'legacy_admin'")
        duplicate_bots = c.execute(
            "SELECT telegram_id FROM bots WHERE status<>'deleted' "
            "GROUP BY telegram_id HAVING COUNT(*)>1"
        ).fetchall()
        if duplicate_bots:
            raise RuntimeError("Duplicate active Telegram Bot IDs require resolution: " +
                               ", ".join(str(row[0]) for row in duplicate_bots))
        c.execute("UPDATE bots SET token='deleted:' || id WHERE status='deleted'")
        c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_bots_live_telegram_id "
                  "ON bots(telegram_id) WHERE status<>'deleted'")
        series_columns = {row["name"] for row in c.execute("PRAGMA table_info(recurring_series)").fetchall()}
        if "owner_user_id" not in series_columns:
            c.execute("ALTER TABLE recurring_series ADD COLUMN owner_user_id TEXT NOT NULL DEFAULT 'legacy_admin'")
        if "loop_mode" not in series_columns:
            c.execute("ALTER TABLE recurring_series ADD COLUMN loop_mode TEXT NOT NULL DEFAULT 'legacy_interval'")
        if "stop_after_seconds" not in series_columns:
            c.execute("ALTER TABLE recurring_series ADD COLUMN stop_after_seconds INTEGER NOT NULL DEFAULT 0")
        if "started_at" not in series_columns:
            c.execute("ALTER TABLE recurring_series ADD COLUMN started_at INTEGER")
        if "ends_at" not in series_columns:
            c.execute("ALTER TABLE recurring_series ADD COLUMN ends_at INTEGER")
        if "paused_at" not in series_columns:
            c.execute("ALTER TABLE recurring_series ADD COLUMN paused_at INTEGER")
        template_columns = {row["name"] for row in c.execute("PRAGMA table_info(task_templates)").fetchall()}
        if "owner_user_id" not in template_columns:
            c.execute("ALTER TABLE task_templates ADD COLUMN owner_user_id TEXT NOT NULL DEFAULT 'legacy_admin'")
        from migrations import migrate
        migrate(c)
        material_library.migrate(c)
        button_actions.migrate(c)
        c.execute("UPDATE imports SET status='paused' WHERE status='running'")
        legacy = c.execute("SELECT id, token FROM bots WHERE token_encryption_version=0 AND status<>'deleted'").fetchall()
        for item in legacy:
            c.execute("UPDATE bots SET token=?, token_encryption_version=1 WHERE id=?",
                      (encrypt_token(item["token"]), item["id"]))
        defaults = {
          "ad_text":"TG管家免费版：让 Telegram 运营更简单，欢迎体验！",
          "ad_button_text":"TG管家免费版",
          "ad_url":"https://t.me/",
          "auto_join_enabled":"0",
          "auto_join_message":"欢迎加入本群！",
          "forced_ad_mode":"BOTH"
        }
        for k,v in defaults.items():
            c.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)",(k,v))
        c.execute("UPDATE settings SET value=? WHERE key='ad_text' AND value=?",
                  (defaults["ad_text"],"TGAdBot 官方推广：免费 Telegram 群发机器人，欢迎体验！"))
        c.execute("UPDATE settings SET value=? WHERE key='ad_button_text' AND value=?",
                  (defaults["ad_button_text"],"TGAdBot 官方推广"))
        c.execute("""UPDATE delivery_jobs SET status='unknown',
                     last_error='进程在发送过程中退出；Telegram 是否已收到无法确认，请人工核对后处理。',
                     updated_at=? WHERE status='sending'""", (now(),))
        c.execute("""UPDATE join_auto_sends SET status='unknown',
                     last_error='进程在发送过程中退出；Telegram 是否已收到无法确认，请人工核对后处理。',
                     updated_at=? WHERE status='sending'""", (now(),))
        c.execute("""UPDATE task_join_auto_sends SET status='unknown',
                     last_error='进程在发送过程中退出；Telegram 是否已收到无法确认，请人工核对后处理。',
                     updated_at=? WHERE status='sending'""", (now(),))

def setting(key):
    with db() as c:
        row = c.execute("SELECT value FROM settings WHERE key=?",(key,)).fetchone()
        return row["value"] if row else ""

def set_setting(key, value):
    with db() as c:
        c.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",(key,value))

class TelegramAPIError(Exception):
    def __init__(self, code, description, retry_after=None):
        super().__init__(description)
        self.code = code
        self.retry_after = retry_after


def telegram_error_message(error):
    description = str(error).lower()
    if error.retry_after is not None:
        return f"发送太频繁，请等待 {error.retry_after} 秒后再试。"
    if error.code == 429:
        return "发送太频繁，请稍后再试。"
    if error.code == 401:
        return "机器人 Token 已失效，请重新添加有效 Token。"
    if error.code == 409:
        if "webhook" in description:
            return "这个机器人已设置 Webhook，请在原服务中停用 Webhook 后再启用监听。"
        return "这个机器人正在被其他程序监听，请关闭另一处监听后重试。"
    reasons = (
        ("chat not found", "找不到目标群，请确认机器人仍在群内。"),
        ("not enough rights", "机器人没有发送权限，请在群设置中给它相应权限。"),
        ("chat_write_forbidden", "机器人没有发送权限，请检查群组的发送权限。"),
        ("bot was kicked", "机器人已被移出群，请重新邀请后再试。"),
        ("bot is not a member", "机器人已不在目标群，请重新邀请后再试。"),
        ("can't parse entities", "消息文字格式有误，请检查链接和文字格式后再发。"),
        ("message to copy not found", "原素材消息已找不到，请重新采集或选择其他素材。"),
        ("message to forward not found", "原素材消息已找不到，请重新采集或选择其他素材。"),
        ("wrong file identifier", "素材引用已失效，请重新采集后再发。"),
        ("message is too long", "消息内容太长，请缩短文字后再发。"),
        ("caption is too long", "图片或视频说明太长，请缩短说明后再发。"),
    )
    for fragment, message in reasons:
        if fragment in description:
            return message
    if error.code == 403:
        return "机器人无法向这个目标发送消息，请检查群成员状态和发送权限。"
    if error.code >= 500:
        return "Telegram 服务暂时异常，请稍后再试。"
    return f"发送被拒绝，暂时无法确定具体原因（错误码 {error.code}），请检查群权限和消息内容。"


def record_delivery_api_error(job_id, error):
    description = re.sub(r"\b\d{5,}:[A-Za-z0-9_-]{20,}", "[已隐藏]", str(error))
    description = " ".join(description.split())[:400]
    logging.warning("Telegram delivery job=%s code=%s description=%s", job_id, error.code, description)
    reason = str(error).lower()
    status = None
    if "bot was kicked" in reason or "bot is not a member" in reason:
        status = "removed"
    elif any(value in reason for value in ("not enough rights", "chat_write_forbidden", "have no rights to send", "not enough permissions", "bot was blocked")):
        status = "no_permission"
    if status:
        with db() as c:
            c.execute("""UPDATE chats SET status=?,last_seen=? WHERE status<>'deleted'
                AND (bot_id,chat_id) IN (SELECT bot_id,chat_id FROM delivery_jobs WHERE id=?)""",
                (status,now(),job_id))



class PartialDeliveryError(Exception):
    """Telegram accepted only part of a multi-message copy/forward request."""

def api(token, method, payload=None, timeout=35):
    return delivery_v2.request_with_receipt(lambda: _api_request(token, method, payload, timeout), method, payload or {})

def _api_request(token, method, payload=None, timeout=35):
    r = requests.post(f"https://api.telegram.org/bot{token}/{method}", json=payload or {}, timeout=timeout)
    try:
        data = r.json()
    except ValueError as exc:
        raise RuntimeError("Telegram returned a non-JSON response") from exc
    if not data.get("ok"):
        parameters = data.get("parameters") or {}
        raise TelegramAPIError(
            int(data.get("error_code") or r.status_code),
            str(data.get("description") or "Telegram API error"),
            int(parameters["retry_after"]) if parameters.get("retry_after") is not None else None,
        )
    return data["result"]

def now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")

def remember_chat(bot_id, chat):
    if chat.get("type") not in ("group","supergroup","channel"):
        return
    title = chat.get("title") or str(chat["id"])
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        if not c.execute("SELECT 1 FROM bots WHERE id=? AND status='active'", (bot_id,)).fetchone():
            return
        c.execute("""INSERT INTO chats(bot_id,chat_id,title,chat_type,status,last_seen)
        VALUES(?,?,?,?,?,?) ON CONFLICT(bot_id,chat_id) DO UPDATE SET
        title=excluded.title,chat_type=excluded.chat_type,
        last_seen=CASE WHEN chats.status='active' THEN excluded.last_seen ELSE chats.last_seen END""",
        (bot_id,chat["id"],title,chat.get("type"),"active",now()))


def remember_media_message(bot_id, message, *, connection=None):
    """Save Telegram media references plus the original message envelope.

    The source chat/message ids let a later task copy or forward the original
    Telegram message as a whole, preserving its caption and inline keyboard.
    No media bytes are downloaded to this server.
    """
    media_type = None
    media = None
    photos = message.get("photo") or []
    if photos:
        media_type = "photo"
        media = max(photos, key=lambda item: int(item.get("file_size") or 0))
    elif message.get("video"):
        media_type = "video"
        media = message.get("video")
    if not media or not media.get("file_id"):
        return False
    chat = message.get("chat") or {}
    origin = message.get("forward_origin") or {}
    origin_chat = origin.get("chat") or message.get("forward_from_chat") or chat
    source_chat_id = chat.get("id")
    source_title = origin_chat.get("title") or origin_chat.get("username") or chat.get("title") or "Telegram"
    raw_message = json.dumps(message, ensure_ascii=False, separators=(",", ":"))
    with (db() if connection is None else nullcontext(connection)) as c:
        if connection is None:
            c.execute("BEGIN IMMEDIATE")
        if not c.execute("SELECT 1 FROM bots WHERE id=? AND status='active'", (bot_id,)).fetchone():
            return False
        c.execute("""INSERT INTO media_assets
            (bot_id,source_chat_id,source_chat_title,source_message_id,media_type,file_id,file_unique_id,caption,file_size,media_group_id,source_message_json,created_at)
            VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
            ON CONFLICT(bot_id,file_unique_id) DO UPDATE SET
              file_id=excluded.file_id, caption=excluded.caption, file_size=excluded.file_size,
              source_chat_id=excluded.source_chat_id, source_chat_title=excluded.source_chat_title,
              source_message_id=excluded.source_message_id, media_group_id=excluded.media_group_id,
              source_message_json=excluded.source_message_json, created_at=excluded.created_at""",
            (bot_id,source_chat_id,str(source_title),message.get("message_id"),media_type,
             media["file_id"],f"source:{source_chat_id}:{message.get('message_id')}" if source_chat_id is not None and message.get("message_id") is not None else media.get("file_unique_id"),message.get("caption"),media.get("file_size"),
             message.get("media_group_id"),raw_message,now()))
    return True


def load_selected_media_assets(c, bot_id, selected_ids):
    """Load selected media and expand any selected album item to its full album.

    Telegram stores captions/buttons on the album's first message. Expanding a
    selected album item prevents users from accidentally omitting that message
    and losing the edited caption or inline keyboard during copy/forward.
    """
    if not selected_ids:
        return []
    numeric_ids = [int(value) for value in selected_ids]
    if len(numeric_ids) != len(set(numeric_ids)):
        raise ValueError("媒体选择包含重复项目，请重新选择。")
    placeholders = ",".join("?" for _ in numeric_ids)
    selected = c.execute(
        f"SELECT id,media_type,file_id,caption,source_chat_title,created_at,source_chat_id,source_message_id,media_group_id,source_message_json "
        f"FROM media_assets WHERE bot_id=? AND id IN ({placeholders}) ORDER BY id",
        (int(bot_id), *numeric_ids),
    ).fetchall()
    if len(selected) != len(numeric_ids):
        raise ValueError("所选媒体不存在或不属于对应机器人。")

    expanded = {int(row["id"]): row for row in selected}
    album_keys = {
        (row["source_chat_id"], str(row["media_group_id"]))
        for row in selected
        if row["source_chat_id"] is not None and row["media_group_id"]
    }
    for source_chat_id, media_group_id in album_keys:
        album_rows = c.execute(
            "SELECT id,media_type,file_id,caption,source_chat_title,created_at,source_chat_id,source_message_id,media_group_id,source_message_json "
            "FROM media_assets WHERE bot_id=? AND source_chat_id=? AND media_group_id=? ORDER BY source_message_id,id",
            (int(bot_id), source_chat_id, media_group_id),
        ).fetchall()
        for row in album_rows:
            expanded[int(row["id"])] = row

    return [{"id": row["id"], "type": row["media_type"], "file_id": row["file_id"],
             "caption": row["caption"], "source_chat_id": row["source_chat_id"],
             "source_message_id": row["source_message_id"], "media_group_id": row["media_group_id"],
             "source_message_json": row["source_message_json"]}
            for row in sorted(expanded.values(), key=lambda item: (item["source_chat_id"] or 0,
                                                                      item["source_message_id"] or 0,
                                                                      item["id"]))]


def queue_task_join_auto_send(bot_id, chat):
    if chat.get("type") not in ("group", "supergroup"):
        return False
    chat_id = int(chat["id"])
    chat_title = str(chat.get("title") or chat_id)
    current = int(time.time())
    enqueued_tasks = []
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        bot_row = c.execute("SELECT id,status FROM bots WHERE id=? AND status='active'", (bot_id,)).fetchone()
        if not bot_row:
            return False
        chat_row = c.execute("SELECT status FROM chats WHERE bot_id=? AND chat_id=?", (bot_id, chat_id)).fetchone()
        if chat_row and chat_row["status"] in ("removed", "no_permission", "deleted"):
            return False
        tasks = c.execute("""SELECT * FROM tasks
            WHERE auto_join_enabled=1 AND status IN ('running','scheduled','paused','completed','partial')
            ORDER BY id DESC LIMIT 100""").fetchall()
        for task in tasks:
            try:
                selected_bots = {str(x) for x in json.loads(task["bot_ids"] or "[]")}
            except (TypeError, ValueError):
                continue
            if str(bot_id) not in selected_bots:
                continue
            if task["ends_at"] and current >= int(task["ends_at"]):
                continue
            # If finished single/loop task already reached global or per-target end condition:
            # For single-run task (max_success == 1) that is completed/partial, a newly joined group
            # gets its 1 run; if the task was cancelled or failed, it was excluded above.
            if task["status"] in ("completed", "partial") and task["semantics"] == "per_target":
                if int(task["max_success"] or 0) > 1:
                    # Multi-round loop task already finished all rounds / stopped
                    continue
            existing = c.execute(
                "SELECT id FROM delivery_jobs WHERE task_id=? AND bot_id=? AND chat_id=?",
                (task["id"], bot_id, chat_id),
            ).fetchone()
            if existing:
                return True
            seq_row = c.execute("SELECT COALESCE(MAX(sequence_no), -1) + 1 FROM delivery_jobs WHERE task_id=?", (task["id"],)).fetchone()
            seq_no = int(seq_row[0]) if seq_row else 0
            job_status = "paused" if task["status"] == "paused" else "pending"
            next_at = max(current, int(task["scheduled_at"] or 0))
            c.execute(
                """INSERT OR IGNORE INTO delivery_jobs
                   (task_id,bot_id,chat_id,chat_title,sequence_no,rotation_index,status,attempts,next_attempt_at,created_at,updated_at,success_count,asset_cursor)
                   VALUES(?,?,?,?,?,0,?,0,?,?,?,0,0)""",
                (task["id"], bot_id, chat_id, chat_title, seq_no, job_status, next_at, now(), now()),
            )
            try:
                targets = json.loads(task["chat_targets"] or "[]")
            except (TypeError, ValueError):
                targets = []
            target_key = f"{bot_id}:{chat_id}"
            if target_key not in targets:
                targets.append(target_key)
                c.execute("UPDATE tasks SET chat_targets=? WHERE id=?", (json.dumps(targets), task["id"]))
            if task["status"] in ("completed", "partial"):
                c.execute("UPDATE tasks SET status='running' WHERE id=?", (task["id"],))
            enqueued_tasks.append(task["id"])
            break
    for tid in enqueued_tasks:
        update_task_summary(tid)
    return bool(enqueued_tasks)


def claim_task_join_auto_send():
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        row=c.execute("""SELECT j.* FROM task_join_auto_sends j
            JOIN tasks t ON t.id=j.task_id JOIN bots b ON b.id=j.bot_id
            WHERE j.status='pending' AND j.next_attempt_at<=? AND b.status='active'
            ORDER BY j.id LIMIT 1""",(int(time.time()),)).fetchone()
        if not row: return None
        cur=c.execute("UPDATE task_join_auto_sends SET status='sending',attempts=attempts+1,updated_at=? WHERE id=? AND status='pending'",
                      (now(),row["id"]))
        if cur.rowcount != 1: return None
        claimed=dict(row); claimed["attempts"]=int(row["attempts"])+1
        return claimed


def queue_auto_join_send(bot_id, chat):
    chat_type=chat.get("type")
    if chat_type not in ("group","supergroup"):
        return False
    if setting("auto_join_enabled") != "1":
        return False
    message=setting("auto_join_message").strip()
    if not message:
        return False
    timestamp=int(time.time())+5
    with db() as c:
        c.execute("""INSERT OR IGNORE INTO join_auto_sends
            (bot_id,chat_id,chat_title,status,next_attempt_at,attempts,created_at,updated_at)
            VALUES(?,?,?,'pending',?,0,?,?)""",
            (bot_id,int(chat["id"]),str(chat.get("title") or chat.get("username") or chat["id"]),
             timestamp,now(),now()))
    return True

def claim_join_auto_send():
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        row=c.execute("""SELECT j.* FROM join_auto_sends j
            JOIN bots b ON b.id=j.bot_id
            WHERE j.status='pending' AND j.next_attempt_at<=? AND b.status='active'
            ORDER BY j.id LIMIT 1""",(int(time.time()),)).fetchone()
        if not row: return None
        cur=c.execute("""UPDATE join_auto_sends SET status='sending',attempts=attempts+1,updated_at=?
                         WHERE id=? AND status='pending'""",(now(),row["id"]))
        if cur.rowcount != 1: return None
        claimed=dict(row); claimed["attempts"]=int(row["attempts"])+1
        return claimed

def process_join_auto_send(job):
    with db() as c:
        bot=c.execute("SELECT token FROM bots WHERE id=? AND status='active'",(job["bot_id"],)).fetchone()
    if not bot:
        with db() as c:
            c.execute("UPDATE join_auto_sends SET status='failed',last_error=?,updated_at=? WHERE id=?",
                      ("机器人不存在或已停用",now(),job["id"]))
        return
    try:
        send_one(decrypt_token(bot["token"]),job["chat_id"],setting("auto_join_message"),[],
                 forced_ad_mode())
        with db() as c:
            c.execute("UPDATE join_auto_sends SET status='sent',last_error=NULL,updated_at=? WHERE id=?",
                      (now(),job["id"]))
    except TelegramAPIError as exc:
        if exc.retry_after is not None:
            with db() as c:
                c.execute("UPDATE join_auto_sends SET status='pending',next_attempt_at=?,last_error=?,updated_at=? WHERE id=?",
                          (int(time.time())+max(1,exc.retry_after),"Telegram 限流，等待后重试",now(),job["id"]))
        else:
            with db() as c:
                c.execute("UPDATE join_auto_sends SET status='failed',last_error=?,updated_at=? WHERE id=?",
                          (telegram_error_message(exc),now(),job["id"]))
    except requests.exceptions.RequestException:
        with db() as c:
            c.execute("UPDATE join_auto_sends SET status='unknown',last_error=?,updated_at=? WHERE id=?",
                      ("发送结果不确定，为避免重复发送已停止自动重试",now(),job["id"]))
    except Exception as exc:
        with db() as c:
            c.execute("UPDATE join_auto_sends SET status='failed',last_error=?,updated_at=? WHERE id=?",
                      (type(exc).__name__,now(),job["id"]))


def record_bot_api_status(bot_id, status, error=None):
    """Persist the last Telegram API result separately from the saved-bot status."""
    with db() as c:
        if status == "connected":
            c.execute("UPDATE bots SET last_api_status='connected',last_api_error=NULL,last_api_ok_at=? WHERE id=? AND status='active'", (now(), bot_id))
        else:
            c.execute("UPDATE bots SET last_api_status='error',last_api_error=? WHERE id=? AND status<>'deleted'", (str(error or "Telegram API 连接异常")[:160], bot_id))


def poll_bot(bot_id, token, stop_event):
    logging.info("Polling started for bot id=%s", bot_id)
    while not stop_event.is_set():
        try:
            with db() as c:
                row = c.execute("SELECT offset,status FROM bots WHERE id=?",(bot_id,)).fetchone()
            if not row or row["status"] != "active":
                break
            updates = api(token,"getUpdates",{
                "offset":row["offset"],"timeout":POLL_TIMEOUT,
                "allowed_updates":["message","edited_message","channel_post","edited_channel_post","my_chat_member","callback_query"]
            },timeout=POLL_TIMEOUT+8)
            record_bot_api_status(bot_id, "connected")
            for upd in updates:
                with db() as c:
                    active = c.execute("SELECT 1 FROM bots WHERE id=? AND status='active'", (bot_id,)).fetchone()
                if stop_event.is_set() or not active:
                    break
                if "my_chat_member" in upd:
                    member_update=upd["my_chat_member"]
                    chat=member_update.get("chat",{})
                    remember_chat(bot_id, chat)
                    old_status=(member_update.get("old_chat_member") or {}).get("status")
                    new_status=(member_update.get("new_chat_member") or {}).get("status")
                    update_chat_membership(bot_id, chat, member_update.get("new_chat_member") or {}, member_update.get("old_chat_member") or {})
                    if old_status in ("left","kicked") and new_status in ("member","administrator","creator"):
                        if not queue_task_join_auto_send(bot_id,chat):
                            queue_auto_join_send(bot_id,chat)
                for message_key in ('message','edited_message','channel_post','edited_channel_post'):
                    if message_key in upd:
                        message = upd[message_key]
                        remember_chat(bot_id, message.get('chat',{}))
                        material_library.collect(sys.modules[__name__], bot_id, message, require_source=True)
                handled = button_actions.dispatch(sys.modules[__name__], bot_id, token, upd) if ('message' in upd or 'callback_query' in upd) else False
                if 'callback_query' in upd and not handled:
                    api(token,'answerCallbackQuery',{'callback_query_id':upd['callback_query']['id'],'text':'该按钮尚未配置动作'})
                with db() as c:
                    c.execute("UPDATE bots SET offset=? WHERE id=? AND status='active'",(upd["update_id"]+1,bot_id))
        except Exception as e:
            if isinstance(e, requests.exceptions.RequestException):
                safe_error = "Telegram 网络连接失败（检查 DNS、出站 HTTPS/443 和服务器防火墙）"
            elif isinstance(e, TelegramAPIError):
                safe_error = telegram_error_message(e)
                if getattr(e, "code", None) == 401:
                    with db() as c:
                        c.execute("UPDATE bots SET status='invalid_token' WHERE id=? AND status='active'", (bot_id,))
                    stop_event.set()
            else:
                safe_error = f"监听处理异常（{type(e).__name__}）"
            try:
                record_bot_api_status(bot_id, "error", safe_error)
            except Exception as status_error:
                logging.warning("Could not persist Telegram status for bot %s: %s", bot_id, type(status_error).__name__)
            logging.warning("Polling bot %s failed: %s",bot_id,type(e).__name__)
            stop_event.wait(4)
    logging.info("Polling stopped for bot id=%s",bot_id)

def start_pollers():
    if not POLLING_ENABLED: return
    with db() as c:
        rows=c.execute("SELECT id,token,token_encryption_version FROM bots WHERE status='active'").fetchall()
    for row in rows:
        start_bot_poller(row["id"], row["token"])


def start_bot_poller(bot_id, encrypted_token):
    with polling_lock:
        existing = polling_threads.get(bot_id)
        if existing and existing.is_alive():
            return
        stop_event = threading.Event()
        thread = threading.Thread(
            target=poll_bot, args=(bot_id, decrypt_token(encrypted_token), stop_event), daemon=True
        )
        stop_events[bot_id] = stop_event
        polling_threads[bot_id] = thread
        thread.start()

def ad_markup(user_buttons, mode, ad_button_text=None, ad_url=None):
    if isinstance(user_buttons, dict) and "keyboard" in user_buttons:
        return user_buttons
    rows=[]
    if mode in ("OFFICIAL_BUTTON_FIRST_ROW","BUTTON_ONLY","BOTH"):
        rows.append([{"text":ad_button_text or setting("ad_button_text") or "官方广告",
                      "url":ad_url or setting("ad_url")}])
    rows.extend(user_buttons)
    return {"inline_keyboard":rows} if rows else None

def update_chat_membership(bot_id, chat, member, old_member=None):
    status = member.get("status")
    old_status = (old_member or {}).get("status")
    if status in ("left", "kicked"):
        state = "removed"
    elif status == "restricted" and not member.get("can_send_messages", False):
        state = "no_permission"
    elif chat.get("type") == "channel" and status == "administrator" and not member.get("can_post_messages", False):
        state = "no_permission"
    elif status in ("member", "administrator", "creator") or (status == "restricted" and member.get("can_send_messages")):
        state = "active"
    else:
        return
    explicit_recovery = state == "active" and old_status in ("left", "kicked", "restricted")
    with db() as c:
        if explicit_recovery:
            c.execute(
                """INSERT INTO chats(bot_id,chat_id,title,chat_type,status,last_seen)
                   VALUES(?,?,?,?,?,?)
                   ON CONFLICT(bot_id,chat_id) DO UPDATE SET
                   title=COALESCE(excluded.title,chats.title),
                   chat_type=COALESCE(excluded.chat_type,chats.chat_type),
                   status='active',last_seen=excluded.last_seen""",
                (bot_id, chat.get("id"), chat.get("title") or str(chat.get("id")), chat.get("type"), "active", now()),
            )
        else:
            c.execute("UPDATE chats SET status=?,last_seen=? WHERE bot_id=? AND chat_id=? AND status<>'deleted'",
                      (state, now(), bot_id, chat.get("id")))


def restore_prompt_editor(raw):
    config = json.loads(raw)
    with db() as c:
        for row in config.get("rows", []):
            for item in row:
                trigger = item.get("target", "")
                if item.get("kind") != "CALLBACK" or not trigger.startswith("prompt:"):
                    continue
                action = c.execute("SELECT a.body FROM button_actions a JOIN bots b ON b.id=a.bot_id WHERE a.trigger=? AND b.owner_user_id=? AND a.mode='inline' AND a.kind='alert' LIMIT 1", (trigger,current_owner_id())).fetchone()
                if action:
                    item.update(kind="PROMPT", target=action["body"])
    return json.dumps(config, ensure_ascii=False)


def prompt_trigger(body):
    import hashlib
    return "prompt:" + hashlib.sha256(body.encode("utf-8")).hexdigest()[:48]


def bind_prompt_actions(c, raw, bot_ids):
    if not (raw or "").lstrip().startswith("{"):
        return
    for row in json.loads(raw).get("rows", []):
        for item in row:
            if item.get("kind", "").upper() == "PROMPT":
                body = str(item.get("target", ""))
                for bot_id in bot_ids:
                    c.execute("INSERT OR IGNORE INTO button_actions(bot_id,trigger,kind,body,mode) VALUES(?,?,'alert',?,'inline')",
                              (bot_id, prompt_trigger(body), body))


def parse_buttons(raw):
    raw = raw or ""
    if raw.lstrip().startswith("{"):
        try:
            data = json.loads(raw)
        except (TypeError, json.JSONDecodeError) as exc:
            raise ValueError("按钮配置格式无效，请重新编辑按钮。") from exc
        if not isinstance(data, dict):
            raise ValueError("按钮配置格式无效，请重新编辑按钮。")
        mode = data.get("mode", "inline")
        if mode not in ("inline", "reply"):
            raise ValueError("未知键盘类型")
        rows = data.get("rows", [])
        if not isinstance(rows, list) or len(rows) > 20:
            raise ValueError("最多20行按钮")
        result=[]
        for row in rows:
            if not isinstance(row,list) or not 1 <= len(row) <= 2:
                raise ValueError("每行1至2个按钮")
            parsed=[]
            for button in row:
                if not isinstance(button,dict): raise ValueError("按钮数据格式错误")
                raw_text = button.get("text", "")
                text = str(raw_text).strip() if raw_text is not None else ""
                if not text or len(text)>64: raise ValueError("按钮文字须为1至64字符")
                if mode == "reply": parsed.append({"text":text}); continue
                raw_kind = button.get("kind", "URL")
                if not isinstance(raw_kind, str):
                    raise ValueError("按钮类型只能是 URL 或 CALLBACK")
                kind = raw_kind.upper()
                target = str(button.get("target", "") or "")
                if kind == "URL":
                    u=urlparse(target)
                    if u.scheme not in ("http","https") or not u.netloc: raise ValueError("无效按钮链接")
                    parsed.append({"text":text,"url":target})
                elif kind == "PROMPT":
                    if not target.strip() or len(target) > 200:
                        raise ValueError("提示内容须为 1 至 200 字符")
                    parsed.append({"text":text,"callback_data":prompt_trigger(target)})
                elif kind == "CALLBACK":
                    if not 1 <= len(target.encode("utf-8")) <= 64: raise ValueError("回调数据须为1至64字节")
                    parsed.append({"text":text,"callback_data":target})
                else: raise ValueError("未知按钮类型")
            result.append(parsed)
        return {"keyboard":result,"resize_keyboard":True} if mode == "reply" and result else result
    rows=[]
    for line in raw.splitlines():
        line=line.strip()
        if not line: continue
        # format: text | URL | https://example.com
        parts=[x.strip() for x in line.split("|",2)]
        if len(parts)!=3: raise ValueError("按钮格式错误，每行使用：按钮文字 | URL或回调 | 目标")
        text,kind,target=parts
        if not text: raise ValueError("按钮文字不能为空")
        if kind.upper()=="URL":
            p=urlparse(target)
            if p.scheme not in ("http","https") or not p.netloc: raise ValueError("按钮链接必须是有效 http/https 地址")
            rows.append([{"text":text,"url":target}])
        elif kind.upper()=="CALLBACK":
            if len(("act:"+target).encode("utf-8")) > 64: raise ValueError("回调数据超过64字节")
            rows.append([{"text":text,"callback_data":("act:"+target)}])
        else:
            raise ValueError("按钮类型只能是 URL 或 CALLBACK")
    return rows

def send_one(token, chat_id, body, buttons, ad_mode=None, ad_text=None, ad_button_text=None, ad_url=None,
             media_path=None, media_type=None):
    ad_mode = ad_mode or forced_ad_mode()
    text=body or ""
    forced_text = ad_text if ad_text is not None else setting("ad_text")
    if ad_mode in ("TEXT_ONLY", "BOTH") and forced_text:
        text = text.rstrip() + "\n\n" + forced_text if text.strip() else forced_text
    markup=ad_markup(buttons,ad_mode,ad_button_text=ad_button_text,ad_url=ad_url)
    if isinstance(buttons,dict) and "keyboard" in buttons and ad_mode in ("BUTTON_ONLY","BOTH","OFFICIAL_BUTTON_FIRST_ROW"):
        text += "\n\n" + (ad_button_text or setting("ad_button_text") or "官方广告") + "：" + (ad_url or setting("ad_url") or "")
    if not media_path:
        if len(text) > 4096:
            raise ValueError("Telegram 文字消息超过 4096 字符限制")
        payload={"chat_id":chat_id,"text":text}
        if markup: payload["reply_markup"]=markup
        return api(token,"sendMessage",payload)
    if media_type not in ("photo","video","document"):
        raise ValueError("不支持的媒体类型")
    if len(text) > 1024:
        raise ValueError("Telegram 媒体说明文字超过 1024 字符限制")
    if not os.path.isfile(media_path):
        raise FileNotFoundError("媒体文件不存在")
    method={"photo":"sendPhoto","video":"sendVideo","document":"sendDocument"}[media_type]
    payload={"chat_id":chat_id,"caption":text}
    if markup: payload["reply_markup"]=json.dumps(markup,ensure_ascii=False)
    mime=mimetypes.guess_type(media_path)[0] or "application/octet-stream"
    def upload():
        with open(media_path,"rb") as media:
            response=requests.post(
                f"https://api.telegram.org/bot{token}/{method}",
                data=payload,
                files={media_type:(os.path.basename(media_path),media,mime)},
                timeout=120,
            )
        try:
            data=response.json()
        except ValueError as exc:
            raise RuntimeError("Telegram returned a non-JSON response") from exc
        if not data.get("ok"):
            parameters=data.get("parameters") or {}
            raise TelegramAPIError(
                int(data.get("error_code") or response.status_code),
                str(data.get("description") or "Telegram API error"),
                int(parameters["retry_after"]) if parameters.get("retry_after") is not None else None,
            )
        return data["result"]
    with open(media_path,"rb") as source:
        digest = hashlib.file_digest(source,"sha256").hexdigest()
    return delivery_v2.request_with_receipt(upload,method,{**payload,"file_sha256":digest})



def _source_message_payload(asset):
    """Return the original Telegram message envelope saved with a media asset."""
    raw = asset.get("source_message_json")
    if isinstance(raw, dict):
        return raw
    if isinstance(raw, str) and raw.strip():
        try:
            value = json.loads(raw)
            return value if isinstance(value, dict) else {}
        except (TypeError, ValueError):
            return {}
    return {}


def _source_inline_keyboard(assets):
    """Find the original inline keyboard, usually attached to the first album item."""
    for asset in assets:
        markup = _source_message_payload(asset).get("reply_markup")
        if isinstance(markup, dict) and isinstance(markup.get("inline_keyboard"), list):
            return markup
    return None


def _attach_source_keyboard(token, chat_id, message_id, markup):
    """Attach the source keyboard after copy/forward, including callback buttons.

    Telegram's forward methods may omit some callback-button types, and
    copyMessages has no reply_markup parameter. Editing the first copied message
    restores the complete original inline keyboard without reconstructing it.
    """
    if not markup or not message_id:
        return None
    try:
        return api(token, "editMessageReplyMarkup", {
            "chat_id": chat_id,
            "message_id": int(message_id),
            "reply_markup": markup,
        })
    except Exception as exc:
        # The media has already been sent. Retrying the whole job could duplicate
        # the album, so surface an ambiguous partial delivery for manual review.
        raise PartialDeliveryError(
            "素材已发送，但原始按钮恢复失败；投递已标记为 UNKNOWN，请核对目标群后再处理。"
        ) from exc


def _send_source_media_group(token, chat_id, assets, sender_mode):
    """Copy or forward source Telegram messages with captions and inline buttons."""
    grouped = []
    group_positions = {}
    for index, asset in enumerate(assets):
        source_chat = asset.get("source_chat_id")
        source_message = asset.get("source_message_id")
        group_id = asset.get("media_group_id")
        if source_chat is None or source_message is None:
            grouped.append((None, [asset]))
            continue
        key = (int(source_chat), str(group_id)) if group_id else (int(source_chat), f"single:{index}")
        if key in group_positions:
            grouped[group_positions[key]][1].append(asset)
        else:
            group_positions[key] = len(grouped)
            grouped.append((key, [asset]))

    results = []
    use_forward = sender_mode == "show"
    for key, group in grouped:
        markup = _source_inline_keyboard(group)
        if key is None:
            asset = group[0]
            kind = asset.get("type")
            method = "sendPhoto" if kind == "photo" else "sendVideo"
            original = _source_message_payload(asset)
            payload = {"chat_id": chat_id, kind: asset["file_id"]}
            caption = original.get("caption") or asset.get("caption")
            if caption:
                payload["caption"] = caption
            if original.get("caption_entities"):
                payload["caption_entities"] = original["caption_entities"]
            if original.get("show_caption_above_media") is True:
                payload["show_caption_above_media"] = True
            if markup:
                payload["reply_markup"] = markup
            results.append(api(token, method, payload))
            continue

        source_chat = key[0]
        message_ids = sorted(int(item["source_message_id"]) for item in group)
        if len(message_ids) > 1 and not key[1].startswith("single:"):
            method = "forwardMessages" if use_forward else "copyMessages"
            payload = {"chat_id": chat_id, "from_chat_id": source_chat, "message_ids": message_ids}
            result = api(token, method, payload)
            if not isinstance(result, list) or len(result) != len(message_ids):
                raise PartialDeliveryError("Telegram 只处理了部分相册消息；结果已标记为 UNKNOWN，请核对后再继续，避免重复发送。")
            results.append(result)
            if markup:
                first = result[0] if isinstance(result[0], dict) else {}
                _attach_source_keyboard(token, chat_id, first.get("message_id"), markup)
        else:
            method = "forwardMessage" if use_forward else "copyMessage"
            payload = {"chat_id": chat_id, "from_chat_id": source_chat, "message_id": message_ids[0]}
            result = api(token, method, payload)
            results.append(result)
            if markup:
                message_id = result.get("message_id") if isinstance(result, dict) else None
                _attach_source_keyboard(token, chat_id, message_id, markup)
    return results

def _send_task_ad_after_copied_media(token, chat_id, buttons, ad_mode, ad_text, ad_button_text, ad_url):
    mode = ad_mode if ad_mode in ("TEXT_ONLY", "BUTTON_ONLY", "BOTH") else forced_ad_mode()
    text = (ad_text or setting("ad_text")) if mode in ("TEXT_ONLY", "BOTH") else ""
    markup = ad_markup(buttons, mode, ad_button_text=ad_button_text, ad_url=ad_url)
    if isinstance(buttons, dict) and "keyboard" in buttons and mode in ("BUTTON_ONLY", "BOTH", "OFFICIAL_BUTTON_FIRST_ROW"):
        text = (text + "\n\n" if text else "") + (ad_button_text or setting("ad_button_text") or "官方广告") + "：" + (ad_url or setting("ad_url") or "")
    if not text and not markup:
        return None
    payload = {"chat_id": chat_id, "text": text or (ad_button_text or setting("ad_button_text") or " ")}
    if markup:
        payload["reply_markup"] = markup
    return api(token, "sendMessage", payload)


def send_task_content(token, chat_id, body, buttons, ad_mode, ad_text, ad_button_text, ad_url,
                      content_modes, media_assets, sender_mode="hide"):
    """Send text and media; source-backed media is copied/forwarded as a whole."""
    modes = set(content_modes or [])
    assets = [item for item in (media_assets or []) if item.get("type") in ("photo", "video") and item.get("file_id")]
    if not ("text" in modes and (body or "").strip()) and not assets:
        raise ValueError("没有可发送的文字、图片或视频内容")
    mode = ad_mode if ad_mode in ("TEXT_ONLY", "BUTTON_ONLY", "BOTH") else forced_ad_mode()
    forced_text = (ad_text or setting("ad_text")) if mode in ("TEXT_ONLY", "BOTH") else ""
    results = []
    first_item = True
    if "text" in modes and (body or "").strip():
        text = (body or "").strip()
        if forced_text:
            text += "\n\n" + forced_text
        if isinstance(buttons, dict) and "keyboard" in buttons and mode in ("BUTTON_ONLY", "BOTH", "OFFICIAL_BUTTON_FIRST_ROW"):
            text += "\n\n" + (ad_button_text or setting("ad_button_text") or "官方广告") + "：" + (ad_url or setting("ad_url") or "")
        if len(text) > 4096:
            raise ValueError("Telegram 文字消息超过 4096 字符限制")
        markup = ad_markup(buttons, mode, ad_button_text=ad_button_text, ad_url=ad_url)
        payload = {"chat_id": chat_id, "text": text}
        if markup:
            payload["reply_markup"] = markup
        results.append(api(token, "sendMessage", payload))
        first_item = False

    selected_assets = [item for item in assets if item.get("type") in modes]
    if selected_assets:
        # When source references exist, copyMessage removes the original sender
        # attribution; forwardMessage retains it. Telegram performs the copy so
        # original caption/entities/inline keyboard remain attached to the media.
        source_backed = all(item.get("source_chat_id") is not None and item.get("source_message_id") is not None
                            for item in selected_assets)
        if source_backed:
            results.extend(_send_source_media_group(token, chat_id, selected_assets,
                                                    "show" if sender_mode == "show" else "hide"))
            if first_item:
                ad_result = _send_task_ad_after_copied_media(token, chat_id, buttons, mode,
                                                             ad_text, ad_button_text, ad_url)
                if ad_result is not None:
                    results.append(ad_result)
        else:
            # Legacy file_id-only media rows remain sendable after upgrade.
            for index, item in enumerate(selected_assets):
                first = first_item and index == 0
                kind = item["type"]
                caption = forced_text if first and forced_text else (item.get("caption") or "")
                if len(caption) > 1024:
                    raise ValueError("Telegram 媒体说明文字超过 1024 字符限制")
                markup = ad_markup(buttons if first else [], mode if first else "OFF",
                                   ad_button_text=ad_button_text, ad_url=ad_url) if first else None
                payload = {"chat_id": chat_id, kind: item["file_id"]}
                if caption:
                    payload["caption"] = caption
                if markup:
                    payload["reply_markup"] = markup
                if item['file_id'].startswith('local:'):
                    local = os.path.realpath(item['file_id'][6:])
                    if os.path.commonpath([local,os.path.realpath(MEDIA_DIR)]) != os.path.realpath(MEDIA_DIR):
                        raise ValueError('媒体路径超出数据目录')
                    results.append(send_one(token,chat_id,caption,buttons if first else [],'OFF',media_path=local,media_type=kind))
                else:
                    results.append(api(token, "sendPhoto" if kind == "photo" else "sendVideo", payload))
    return results

def process_task_join_auto_send(job):
    with db() as c:
        bot=c.execute("SELECT token FROM bots WHERE id=? AND status='active'",(job["bot_id"],)).fetchone()
        task=c.execute("SELECT * FROM tasks WHERE id=?",(job["task_id"],)).fetchone()
    if not bot or not task:
        with db() as c:
            c.execute("UPDATE task_join_auto_sends SET status='failed',last_error=?,updated_at=? WHERE id=?",
                      ("机器人或原群发任务不存在",now(),job["id"]))
        return
    if task["status"] in ("cancelled", "failed", "paused"):
        with db() as c:
            c.execute("UPDATE task_join_auto_sends SET status='cancelled',last_error=?,updated_at=? WHERE id=?",
                      ("原群发任务已暂停或取消",now(),job["id"]))
        return
    try:
        media_map=json.loads(task["media_assets"] or "{}")
        assets=media_map.get(str(job["bot_id"]), [])
        modes=json.loads(task["content_modes"] or '["text"]')
        rotation=json.loads(task["rotation_messages"] or "[]")
        token=decrypt_token(bot["token"])
        buttons=json.loads(task["buttons"])
        if rotation:
            with db() as c:
                current=c.execute("SELECT rotation_index FROM task_join_auto_sends WHERE id=?",(job["id"],)).fetchone()
            rotation_index=int(current["rotation_index"] or 0) if current else 0
            if rotation_index < 0 or rotation_index > len(rotation):
                raise RuntimeError("入群轮换进度数据无效")
            while rotation_index < len(rotation):
                send_one(token,job["chat_id"],rotation[rotation_index],buttons,task["ad_mode"],
                         ad_text=task["ad_text"],ad_button_text=task["ad_button_text"],ad_url=task["ad_url"])
                rotation_index += 1
                with db() as c:
                    c.execute("UPDATE task_join_auto_sends SET rotation_index=?,updated_at=? WHERE id=? AND status='sending'",
                              (rotation_index,now(),job["id"]))
        else:
            send_task_content(token,job["chat_id"],task["body"],buttons,
                              task["ad_mode"],task["ad_text"],task["ad_button_text"],task["ad_url"],modes,assets,task["sender_mode"] or "hide")
        with db() as c:
            c.execute("UPDATE task_join_auto_sends SET status='sent',last_error=NULL,updated_at=? WHERE id=?",(now(),job["id"]))
    except PartialDeliveryError as exc:
        with db() as c:
            c.execute("UPDATE task_join_auto_sends SET status='unknown',last_error=?,updated_at=? WHERE id=?",
                      (str(exc),now(),job["id"]))
    except TelegramAPIError as exc:
        if exc.retry_after is not None:
            with db() as c:
                c.execute("UPDATE task_join_auto_sends SET status='pending',next_attempt_at=?,last_error=?,updated_at=? WHERE id=?",
                          (int(time.time())+max(1,exc.retry_after),"Telegram 限流，等待后重试",now(),job["id"]))
        else:
            with db() as c:
                c.execute("UPDATE task_join_auto_sends SET status='failed',last_error=?,updated_at=? WHERE id=?",
                          (telegram_error_message(exc),now(),job["id"]))
    except requests.exceptions.RequestException:
        with db() as c:
            c.execute("UPDATE task_join_auto_sends SET status='unknown',last_error=?,updated_at=? WHERE id=?",
                      ("发送结果不确定，为避免重复发送已停止自动重试",now(),job["id"]))
    except Exception as exc:
        with db() as c:
            c.execute("UPDATE task_join_auto_sends SET status='failed',last_error=?,updated_at=? WHERE id=?",
                      (type(exc).__name__,now(),job["id"]))


def cleanup_success_logs(now_dt=None):
    """Expire presentation logs only; queue records remain available to scheduling."""
    current = now_dt or datetime.now(timezone.utc)
    cutoff = (current - timedelta(hours=LOG_RETENTION_HOURS)).isoformat(timespec="seconds")
    with db() as c:
        owners = c.execute("SELECT DISTINCT owner_user_id FROM tasks").fetchall()
        for owner in owners:
            c.execute("INSERT INTO log_visibility(owner_user_id,hidden_before) VALUES(?,?) ON CONFLICT(owner_user_id) DO UPDATE SET hidden_before=MAX(hidden_before,excluded.hidden_before)", (owner[0],cutoff))
    return 0



def pause_task(task_id):
    with db() as c:
        task=c.execute("SELECT * FROM tasks WHERE id=?",(task_id,)).fetchone()
        if not task or task["status"] in ("completed","failed","cancelled","unknown"):
            return False, "该任务不存在或当前状态不能暂停"
        if task["status"] == "paused":
            return False, "任务已暂停"
        c.execute("UPDATE tasks SET paused_at=? WHERE id=?", (int(time.time()), task_id))
        c.execute("UPDATE tasks SET status='paused',result='顾客已手动暂停' WHERE id=?",(task_id,))
        c.execute("""UPDATE delivery_jobs SET status='paused',updated_at=?
                     WHERE task_id=? AND status='pending'""",(now(),task_id))
        c.execute("UPDATE task_join_auto_sends SET status='paused',updated_at=? WHERE task_id=? AND status='pending'",(now(),task_id))
        return True, "任务已暂停；正在发送中的单条消息不会被强制中断"

def resume_task(task_id):
    with db() as c:
        task=c.execute("SELECT * FROM tasks WHERE id=?",(task_id,)).fetchone()
        if not task or task["status"] not in ("paused",):
            return False, "只有已暂停任务可以恢复"
        current = int(time.time())
        paused_for = max(0, current - int(task['paused_at'] or current)) if task['started_at'] else 0
        c.execute("""UPDATE delivery_jobs SET status='pending',next_attempt_at=MAX(next_attempt_at+?, ?, ?),updated_at=?
                     WHERE task_id=? AND status='paused'""",(paused_for,current,task['scheduled_at'] or 0,now(),task_id))
        c.execute("UPDATE tasks SET ends_at=CASE WHEN ends_at IS NOT NULL THEN ends_at+? END,paused_at=NULL,pause_total=pause_total+? WHERE id=?",(paused_for,paused_for,task_id))
        c.execute("UPDATE task_join_auto_sends SET status='pending',next_attempt_at=MAX(next_attempt_at,?),updated_at=? WHERE task_id=? AND status='paused'",(int(time.time()),now(),task_id))
        c.execute("UPDATE tasks SET status='running',result='顾客已恢复任务' WHERE id=?",(task_id,))
        return True, "任务已恢复并重新进入发送队列"

def retry_failed_jobs(task_id):
    with db() as c:
        task=c.execute("SELECT * FROM tasks WHERE id=?",(task_id,)).fetchone()
        if not task or task["status"] in ("cancelled","paused"):
            return False,"任务不存在、已取消或已暂停"
        cur=c.execute("UPDATE delivery_jobs SET status='pending',next_attempt_at=?,last_error=NULL,updated_at=? WHERE task_id=? AND status='failed'",
                      (int(time.time()),now(),task_id))
        if cur.rowcount:
            c.execute("UPDATE tasks SET status='running',result='管理员重新排入失败投递' WHERE id=?",(task_id,))
            return True,f"已重新排入 {cur.rowcount} 条明确失败投递；UNKNOWN 不会自动重试"
        return False,"没有可安全重试的明确失败投递"

def cancel_task(task_id):
    with db() as c:
        task=c.execute("SELECT status,series_id,semantics FROM tasks WHERE id=?",(task_id,)).fetchone()
        if not task or task["status"] in ("completed","failed","cancelled"):
            return False, "该任务不存在或已经结束"
        c.execute("UPDATE tasks SET status='cancelled',result='顾客已取消任务' WHERE id=?",(task_id,))
        if task["series_id"]:
            c.execute("UPDATE recurring_series SET status='cancelled',updated_at=? WHERE id=?",
                      (now(),task["series_id"]))
        c.execute("""UPDATE delivery_jobs SET status='cancelled',updated_at=?
                     WHERE task_id=? AND status IN ('pending','paused')""",(now(),task_id))
        c.execute("UPDATE task_join_auto_sends SET status='cancelled',updated_at=? WHERE task_id=? AND status IN ('pending','paused')",(now(),task_id))
        return True, "任务已取消；已发送消息不会撤回，正在发送的单条消息可能完成"


delivery_worker_thread = None
delivery_worker_stop = threading.Event()

def claim_delivery_job():
    job = delivery_v2.claim(sys.modules[__name__])
    if job is not None:
        return job
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("""SELECT delivery_jobs.* FROM delivery_jobs
            JOIN tasks ON tasks.id=delivery_jobs.task_id
            WHERE tasks.semantics='legacy' AND delivery_jobs.status='pending' AND delivery_jobs.next_attempt_at<=?
              AND tasks.status IN ('running','scheduled')
            ORDER BY delivery_jobs.id LIMIT 1""", (int(time.time()),)).fetchone()
        if not row:
            return None
        cur = c.execute("""UPDATE delivery_jobs SET status='sending', attempts=attempts+1, updated_at=?
                           WHERE id=? AND status='pending'""", (now(), row["id"]))
        if cur.rowcount != 1:
            return None
        c.execute("UPDATE tasks SET status='running' WHERE id=?", (row["task_id"],))
        series = c.execute("SELECT series_id FROM tasks WHERE id=?", (row["task_id"],)).fetchone()
        if series and series["series_id"]:
            started = int(time.time())
            c.execute("""UPDATE recurring_series
                         SET started_at=COALESCE(started_at,?),
                             ends_at=CASE WHEN stop_after_seconds>0 AND ends_at IS NULL
                                          THEN ? + stop_after_seconds ELSE ends_at END,
                             updated_at=?
                         WHERE id=? AND loop_mode='continuous'""",
                      (started, started, now(), series["series_id"]))
        claimed = dict(row)
        claimed["attempts"] = int(row["attempts"]) + 1
        return claimed



def pause_series(series_id):
    with db() as c:
        row=c.execute("SELECT status FROM recurring_series WHERE id=?",(series_id,)).fetchone()
        if not row or row["status"]!="active":
            return False,"只有运行中的循环系列可以暂停"
        c.execute("UPDATE recurring_series SET status='paused',paused_at=?,updated_at=? WHERE id=?",
                  (int(time.time()),now(),series_id))
        return True,"循环系列已暂停；当前正在发送的群组会完成，不再启动下一轮"

def resume_series(series_id):
    with db() as c:
        row=c.execute("SELECT status,paused_at,ends_at FROM recurring_series WHERE id=?",(series_id,)).fetchone()
        if not row or row["status"]!="paused":
            return False,"只有人工暂停的循环系列可以恢复；UNKNOWN 系列必须先核对"
        current=int(time.time())
        paused_for=max(0,current-int(row["paused_at"] or current))
        ends_at=(int(row["ends_at"])+paused_for) if row["ends_at"] is not None else None
        c.execute("UPDATE recurring_series SET status='active',next_run_at=MAX(next_run_at,?),ends_at=?,paused_at=NULL,updated_at=? WHERE id=?",
                  (current,ends_at,now(),series_id))
        return True,"循环系列已恢复；定时停止倒计时已扣除暂停时间"

def cancel_series(series_id):
    with db() as c:
        row=c.execute("SELECT status FROM recurring_series WHERE id=?",(series_id,)).fetchone()
        if not row or row["status"] in ("completed","cancelled","failed"):
            return False,"循环系列不存在或已经结束"
        c.execute("UPDATE recurring_series SET status='cancelled',updated_at=? WHERE id=?",(now(),series_id))
        c.execute("UPDATE tasks SET status='cancelled',result='循环系列已取消' WHERE series_id=? AND status IN ('running','scheduled','paused')",
                  (series_id,))
        c.execute("UPDATE delivery_jobs SET status='cancelled',updated_at=? WHERE task_id IN (SELECT id FROM tasks WHERE series_id=?) AND status IN ('pending','paused')",
                  (now(),series_id))
        return True,"循环系列已取消；已发送内容不会撤回"


def process_recurring_series():
    current_time = int(time.time())
    with db() as c:
        series_rows = c.execute("SELECT * FROM recurring_series WHERE status='active' AND next_run_at<=? ORDER BY id LIMIT 20",
                                (current_time,)).fetchall()
    created = 0
    for series in series_rows:
        continuous = (series["loop_mode"] or "legacy_interval") == "continuous"
        # A duration is measured from the first actual delivery, not from the
        # moment a future-scheduled task was created. Expiry prevents another
        # target group/round from being started; an already-sending group is
        # allowed to finish its current A/B/C sequence.
        if continuous and series["ends_at"] is not None and current_time >= int(series["ends_at"]):
            with db() as c:
                c.execute("UPDATE recurring_series SET status='completed',updated_at=? WHERE id=?",
                          (now(),series["id"]))
                if series["last_task_id"]:
                    c.execute("UPDATE delivery_jobs SET status='cancelled',last_error='循环定时已到，停止后续群组',updated_at=? WHERE task_id=? AND status IN ('pending','paused')",
                              (now(),series["last_task_id"]))
            if series["last_task_id"]:
                update_task_summary(series["last_task_id"])
            continue

        with db() as c:
            previous = c.execute("SELECT status FROM tasks WHERE id=?", (series["last_task_id"],)).fetchone()
        if not previous:
            with db() as c:
                c.execute("UPDATE recurring_series SET status='failed',updated_at=? WHERE id=?", (now(),series["id"]))
            continue
        if previous["status"] in ("running","scheduled","paused"):
            continue
        if previous["status"] == "unknown":
            with db() as c:
                c.execute("UPDATE recurring_series SET status='paused_unknown',updated_at=? WHERE id=?", (now(),series["id"]))
            continue
        if int(series["max_runs"]) > 0 and int(series["runs_created"]) >= int(series["max_runs"]):
            with db() as c:
                c.execute("UPDATE recurring_series SET status='completed',updated_at=? WHERE id=?", (now(),series["id"]))
            continue
        config = json.loads(series["config_json"])
        targets = []
        with db() as c:
            for key in config["chat_targets"]:
                bid,cid = map(int,key.split(":"))
                if str(bid) in config["bot_ids"]:
                    bot = c.execute("SELECT id FROM bots WHERE id=? AND status='active'",(bid,)).fetchone()
                    chat = c.execute("SELECT title FROM chats WHERE bot_id=? AND chat_id=? AND status='active'",(bid,cid)).fetchone()
                    if bot and chat:
                        targets.append((bid,cid,chat["title"]))
        if not targets:
            with db() as c:
                c.execute("UPDATE recurring_series SET status='failed',updated_at=? WHERE id=?", (now(),series["id"]))
            continue
        run_at = current_time if continuous else int(series["next_run_at"])
        with db() as c:
            cur = c.execute("""INSERT INTO tasks (bot_ids,chat_targets,body,buttons,ad_mode,ad_text,ad_button_text,ad_url,status,created_at,media_path,media_type,scheduled_at,rotation_messages,series_id,content_modes,media_assets,auto_join_enabled,owner_user_id,send_gap_seconds,sender_mode)
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                (json.dumps(config["bot_ids"]),json.dumps(config["chat_targets"]),config["body"],
                 json.dumps(config["buttons"],ensure_ascii=False),config["ad_mode"],config["ad_text"],
                 config["ad_button_text"],config["ad_url"],"scheduled",now(),config.get("media_path"),
                 config.get("media_type"),run_at,json.dumps(config.get("rotation_messages",[]),ensure_ascii=False),series["id"],
                 json.dumps(config.get("content_modes",["text"])),json.dumps(config.get("media_assets",{})),
                 int(bool(config.get("auto_join_enabled"))),series["owner_user_id"],
                 platform_send_gap_seconds(),
                 config.get("sender_mode", "hide")))
            task_id = cur.lastrowid
            for sequence_no,(bid,cid,title) in enumerate(targets):
                c.execute("INSERT INTO delivery_jobs (task_id,bot_id,chat_id,chat_title,sequence_no,status,attempts,next_attempt_at,created_at,updated_at) VALUES(?,?,?,?,?,'pending',0,?,?,?)",
                    (task_id,bid,cid,title,sequence_no,run_at,now(),now()))
            runs_created = int(series["runs_created"]) + 1
            next_run_at = run_at if continuous else run_at + int(series["interval_seconds"])
            c.execute("UPDATE recurring_series SET runs_created=?,last_task_id=?,next_run_at=?,updated_at=? WHERE id=?",
                      (runs_created,task_id,next_run_at,now(),series["id"]))
        created += 1
    return created

def update_task_summary(task_id):
    with db() as c:
        current = c.execute("SELECT status,series_id,semantics FROM tasks WHERE id=?", (task_id,)).fetchone()
        if not current or current["status"] in ("paused","cancelled"):
            return
        rows = c.execute("SELECT status, COUNT(*) AS n FROM delivery_jobs WHERE task_id=? GROUP BY status",
                         (task_id,)).fetchall()
        counts = {r["status"]: r["n"] for r in rows}
        total = sum(counts.values())
        sent = counts.get("sent", 0)
        failed = counts.get("failed", 0)
        unknown = counts.get("unknown", 0)
        cancelled = counts.get("cancelled", 0)
        pending = counts.get("pending", 0) + counts.get("sending", 0)
        if pending:
            status = "running"
        elif unknown:
            status = "unknown"
        elif cancelled and sent:
            status = "partial"
        elif cancelled and not sent:
            status = "cancelled"
        elif failed and sent:
            status = "partial"
        elif failed:
            status = "failed"
        else:
            status = "completed"
        confirmed = sent
        if current["semantics"] == "per_target":
            confirmed = c.execute("SELECT COALESCE(SUM(success_count),0) FROM delivery_jobs WHERE task_id=?", (task_id,)).fetchone()[0]
        result = f"总目标 {total}；成功 {confirmed}；失败 {failed}；结果未知 {unknown}；已停止 {cancelled}；待处理 {pending}"
        c.execute("UPDATE tasks SET status=?,result=? WHERE id=?", (status,result,task_id))
        if current["series_id"] and status in ("completed","partial","failed"):
            series=c.execute("SELECT runs_created,max_runs FROM recurring_series WHERE id=?",
                             (current["series_id"],)).fetchone()
            if series and int(series["max_runs"]) > 0 and int(series["runs_created"]) >= int(series["max_runs"]):
                c.execute("UPDATE recurring_series SET status='completed',updated_at=? WHERE id=?",
                          (now(),current["series_id"]))

def platform_send_gap_seconds():
    try:
        value = float(setting("default_send_gap_seconds") or DEFAULT_TASK_SEND_GAP_SECONDS)
    except (ValueError, TypeError):
        value = DEFAULT_TASK_SEND_GAP_SECONDS
    if not math.isfinite(value):
        value = DEFAULT_TASK_SEND_GAP_SECONDS
    return min(MAX_TASK_SEND_GAP_SECONDS, max(MIN_TASK_SEND_GAP_SECONDS, value))


def task_send_gap_seconds(task_id):
    min_gap = platform_send_gap_seconds()
    with db() as c:
        row = c.execute("SELECT send_gap_seconds FROM tasks WHERE id=?", (task_id,)).fetchone()
    if not row or row["send_gap_seconds"] is None:
        return min_gap
    try:
        saved = float(row["send_gap_seconds"])
    except (TypeError, ValueError):
        return min_gap
    if not math.isfinite(saved):
        return min_gap
    return min(MAX_TASK_SEND_GAP_SECONDS, max(min_gap, saved))


@app.get("/settings/delivery-interval")
@login_required
def delivery_interval():
    response = jsonify(seconds=platform_send_gap_seconds())
    response.headers["Cache-Control"] = "no-store"
    return response


def defer_task_delivery_jobs(task_id):
    with db() as c:
        task = c.execute("SELECT semantics FROM tasks WHERE id=?", (task_id,)).fetchone()
    if task and task["semantics"] == "per_target":
        return
    """Pace only the remaining jobs in this task; do not block other users' tasks."""
    ready_at = math.ceil(time.time() + task_send_gap_seconds(task_id))
    with db() as c:
        c.execute("""UPDATE delivery_jobs SET next_attempt_at=MAX(next_attempt_at, ?)
                     WHERE task_id=? AND status='pending'""", (ready_at, task_id))


def process_delivery_job(job):
    with db() as c:
        modern = c.execute("SELECT * FROM tasks WHERE id=?", (job["task_id"],)).fetchone()
    if modern and modern["semantics"] == "per_target":
        return delivery_v2.process(sys.modules[__name__], job, modern)
    with db() as c:
        bot = c.execute("SELECT token FROM bots WHERE id=? AND status='active'", (job["bot_id"],)).fetchone()
    if not bot:
        with db() as c:
            c.execute("UPDATE delivery_jobs SET status='failed',last_error=?,updated_at=? WHERE id=?",
                      ("机器人不存在或已停用",now(),job["id"]))
        update_task_summary(job["task_id"])
        return

    with db() as c:
        task = c.execute("SELECT body,buttons,ad_mode,ad_text,ad_button_text,ad_url,media_path,media_type,rotation_messages,content_modes,media_assets,sender_mode FROM tasks WHERE id=?", (job["task_id"],)).fetchone()
    if not task:
        with db() as c:
            c.execute("UPDATE delivery_jobs SET status='failed',last_error=?,updated_at=? WHERE id=?",
                      ("任务记录不存在",now(),job["id"]))
        update_task_summary(job["task_id"])
        return

    try:
        token = decrypt_token(bot["token"])
        rotation = json.loads(task["rotation_messages"] or "[]")
        buttons = json.loads(task["buttons"])
        if rotation:
            # Each target group receives the complete A -> B -> C sequence.
            # The progress cursor is persisted after every successful Telegram
            # response, so an explicitly failed job can resume at the next item.
            with db() as c:
                current = c.execute("SELECT rotation_index FROM delivery_jobs WHERE id=?", (job["id"],)).fetchone()
            rotation_index = int(current["rotation_index"] or 0) if current else 0
            if rotation_index < 0 or rotation_index > len(rotation):
                raise RuntimeError("轮换进度数据无效")
            while rotation_index < len(rotation):
                send_one(token, job["chat_id"], rotation[rotation_index], buttons, task["ad_mode"],
                         ad_text=task["ad_text"], ad_button_text=task["ad_button_text"], ad_url=task["ad_url"])
                rotation_index += 1
                with db() as c:
                    c.execute("UPDATE delivery_jobs SET rotation_index=?,updated_at=? WHERE id=? AND status='sending'",
                              (rotation_index, now(), job["id"]))
        elif task["media_path"]:
            # Backward compatibility for pre-update queued media tasks.
            send_one(token, job["chat_id"], task["body"], buttons, task["ad_mode"],
                     ad_text=task["ad_text"], ad_button_text=task["ad_button_text"], ad_url=task["ad_url"],
                     media_path=task["media_path"], media_type=task["media_type"])
        else:
            media_map=json.loads(task["media_assets"] or "{}")
            assets=media_map.get(str(job["bot_id"]), [])
            modes=json.loads(task["content_modes"] or '["text"]')
            if modes == ["text"] and not assets:
                send_one(token,job["chat_id"],task["body"],buttons,task["ad_mode"],ad_text=task["ad_text"],
                         ad_button_text=task["ad_button_text"],ad_url=task["ad_url"])
            else:
                send_task_content(token,job["chat_id"],task["body"],buttons,task["ad_mode"],task["ad_text"],
                                  task["ad_button_text"],task["ad_url"],modes,assets,task["sender_mode"] or "hide")
        with db() as c:
            c.execute("UPDATE delivery_jobs SET status='sent',last_error=NULL,updated_at=? WHERE id=?",
                      (now(),job["id"]))
    except PartialDeliveryError as exc:
        with db() as c:
            c.execute("UPDATE delivery_jobs SET status='unknown',last_error=?,updated_at=? WHERE id=?",
                      (str(exc),now(),job["id"]))
    except TelegramAPIError as exc:
        record_delivery_api_error(job["id"], exc)
        if exc.code == 401:
            with db() as c:
                c.execute("UPDATE bots SET status='invalid_token',last_api_status='error',last_api_error='Telegram 拒绝 Token（401）' WHERE id=? AND status='active'",
                          (job["bot_id"],))
                affected = [row[0] for row in c.execute("SELECT DISTINCT task_id FROM delivery_jobs WHERE bot_id=? AND status='pending'", (job["bot_id"],)).fetchall()]
                c.execute("UPDATE delivery_jobs SET status='failed',last_error='机器人 Token 已失效（401）',updated_at=? WHERE bot_id=? AND status='pending'",
                          (now(), job["bot_id"]))
            for affected_task_id in affected:
                update_task_summary(affected_task_id)
        elif exc.code == 403:
            with db() as c:
                c.execute("UPDATE chats SET status=CASE WHEN status IN ('removed','no_permission') THEN status ELSE 'no_permission' END,last_seen=? WHERE bot_id=? AND chat_id=? AND status<>'deleted'",
                          (now(), job["bot_id"], job["chat_id"]))
        if exc.retry_after is not None:
            delay = max(1, exc.retry_after)
            retry_at = int(time.time()) + delay
            with db() as c:
                c.execute("UPDATE delivery_jobs SET status='pending',next_attempt_at=MAX(next_attempt_at,?),last_error=?,updated_at=? WHERE id=?",
                          (retry_at, f"Telegram 限流，等待 {delay} 秒后重试",now(),job["id"]))
                # Telegram rate limits are Bot-scoped: pause this Bot's other queued
                # deliveries too, without blocking unrelated Bots or user accounts.
                c.execute("UPDATE delivery_jobs SET next_attempt_at=MAX(next_attempt_at,?),updated_at=? WHERE bot_id=? AND status='pending' AND id<>?",
                          (retry_at, now(), job["bot_id"], job["id"]))
        elif exc.code >= 500 and job["attempts"] < 5:
            delay = min(300, 2 ** job["attempts"])
            with db() as c:
                c.execute("UPDATE delivery_jobs SET status='pending',next_attempt_at=?,last_error=?,updated_at=? WHERE id=?",
                          (int(time.time())+delay, f"Telegram 服务端错误 {exc.code}，稍后重试",now(),job["id"]))
        else:
            with db() as c:
                c.execute("UPDATE delivery_jobs SET status='failed',last_error=?,updated_at=? WHERE id=?",
                          (telegram_error_message(exc),now(),job["id"]))
    except requests.exceptions.RequestException:
        # A network timeout/reset can happen after Telegram accepted the message.
        # Do not blindly retry: that could duplicate the current rotation item.
        with db() as c:
            c.execute("UPDATE delivery_jobs SET status='unknown',last_error=?,updated_at=? WHERE id=?",
                      ("网络结果不确定；为避免重复发送，已停止自动重试，请人工核对目标群。",now(),job["id"]))
    except Exception as exc:
        with db() as c:
            c.execute("UPDATE delivery_jobs SET status='failed',last_error=?,updated_at=? WHERE id=?",
                      (type(exc).__name__,now(),job["id"]))
    update_task_summary(job["task_id"])

def delivery_worker():
    logging.info("Delivery worker started")
    last_log_cleanup = 0
    while not delivery_worker_stop.is_set():
        if int(time.time()) - last_log_cleanup >= LOG_CLEANUP_INTERVAL_SECONDS:
            try:
                removed = cleanup_success_logs()
                if removed:
                    logging.info("Pruned %s old successful delivery records", removed)
            except Exception as exc:
                logging.error("Success-log cleanup failed: %s", type(exc).__name__)
            last_log_cleanup = int(time.time())
        try:
            process_recurring_series()
        except Exception as exc:
            logging.error("Recurring scheduler error: %s", type(exc).__name__)
        job = claim_delivery_job()
        if job:
            process_delivery_job(job)
            defer_task_delivery_jobs(job["task_id"])
            continue
        task_join_job=claim_task_join_auto_send()
        if task_join_job:
            process_task_join_auto_send(task_join_job)
            delivery_worker_stop.wait(platform_send_gap_seconds())
            continue
        join_job=claim_join_auto_send()
        if join_job:
            process_join_auto_send(join_job)
            delivery_worker_stop.wait(platform_send_gap_seconds())
            continue
        delivery_worker_stop.wait(0.5)
    logging.info("Delivery worker stopped")

def start_delivery_worker():
    global delivery_worker_thread
    if delivery_worker_thread and delivery_worker_thread.is_alive():
        return
    delivery_worker_stop.clear()
    delivery_worker_thread = threading.Thread(target=delivery_worker,daemon=True,name="tgadbot-delivery")
    delivery_worker_thread.start()


BASE = "{% include 'base.html' %}"


@app.template_filter("status_zh")
def status_zh(status):
    return {
        "active": "正常", "invalid_token": "凭据失效", "disabled": "已停用", "connected": "连接正常", "running": "进行中", "scheduled": "待定时发送",
        "pending": "等待处理", "paused": "已暂停", "sending": "发送中",
        "sent": "发送成功", "failed": "发送失败", "unknown": "结果待确认",
        "completed": "已完成", "partial": "部分完成", "cancelled": "已取消",
        "deleted": "已删除", "archived": "已归档", "skipped": "已跳过",
        "done": "已完成", "success": "成功", "error": "失败",
        "paused_unknown": "结果待确认，已暂停", "removed": "异常：已退群或被移出", "no_permission": "异常：没有发送权限",
    }.get(str(status).lower(), "状态待确认")


def page(content, **ctx):
    admin = is_admin_user()
    if session.get("user_id") or session.get("auth_method") or session.get("telegram_user_id"):
        with db() as c:
            notices=c.execute("SELECT * FROM announcements WHERE enabled=1 AND published_at<=? ORDER BY pinned DESC,published_at DESC,id DESC",(int(time.time()),)).fetchall()
        content = """<section class="card"><h2>平台公告</h2>{% for n in notices %}<article><h3>{{n.title}}</h3><p style="white-space:pre-wrap">{{n.body}}</p></article>{% endfor %}{% if official_group %}<a href="{{official_group}}" target="_blank" rel="noopener">加入官方群</a>{% endif %}{% if notice_admin %}<p><a href="/admin/announcements">管理公告与官方群</a></p>{% endif %}</section>""" + content
        ctx.update(notices=notices,official_group=setting("official_group_url"),notice_admin=admin)
    if 'name="buttons"' in content and 'broadcast-form' in content:
        with db() as c:
            saved_buttons=c.execute('SELECT id,title FROM button_templates WHERE owner_user_id=? ORDER BY id DESC LIMIT 100',(current_owner_id(),)).fetchall()
        ctx['saved_buttons']=saved_buttons
        content = '<section class="card"><label>载入按钮模板<select data-button-template><option value="">选择模板（替换本次按钮配置）</option>{% for b in saved_buttons %}<option value="{{b.id}}">{{b.title}}</option>{% endfor %}</select></label></section>' + content
    try:
        sidebar_links = json.loads(setting("sidebar_links") or "[]")
    except (ValueError, TypeError):
        sidebar_links = []
    ctx["sidebar_links"] = sidebar_links
    ctx["platform_gap"] = platform_send_gap_seconds()
    return render_template_string(BASE,content=Markup(render_template_string(content,**ctx)),is_admin=admin,sidebar_links=sidebar_links)


@app.route("/login", methods=["GET", "POST"])
def login():
    if session.get("authenticated"):
        return redirect(url_for("index"))
    if request.method == "POST":
        ip = request.remote_addr or "unknown"
        if login_is_rate_limited(ip):
            abort(429)
        admin_password = request.form.get("admin_password", "")
        if admin_password and hmac.compare_digest(admin_password, ADMIN_PASSWORD):
            clear_login_failures(ip)
            session.clear()
            session["authenticated"] = True
            session["is_admin"] = True
            session["auth_method"] = "admin_password"
            session.permanent = True
            destination = request.args.get("next", "")
            if not destination.startswith("/") or destination.startswith("//"):
                destination = url_for("index")
            return redirect(destination)
        email = request.form.get("email", "").strip().lower()
        password = request.form.get("password", "")
        user = authenticate_local_user(email, password)
        if user:
            clear_login_failures(ip)
            with db() as c:
                c.execute("UPDATE user_accounts SET last_login_at=? WHERE id=?", (now(), user["id"]))
            session.clear()
            session["authenticated"] = True
            session["user_id"] = user["id"]
            session["auth_method"] = "local_password"
            session.permanent = True
            destination = request.args.get("next", "")
            if not destination.startswith("/") or destination.startswith("//"):
                destination = url_for("index")
            return redirect(destination)
        record_login_failure(ip)
        flash("账号或密码错误，或账号已被平台停用。")
    content = '''
    <div class="card"><h2>TG管家免费版 · 用户登录</h2>
    <form method="post"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <label>邮箱账号</label><input type="email" name="email" required autocomplete="username" placeholder="name@example.com">
    <label>登录密码</label><input type="password" name="password" required autocomplete="current-password">
    <button type="submit">登录</button> <a class="btn secondary" href="/register">免费注册</a></form>
    <p class="muted">一个账号管理自己的 Telegram 机器人、群组、素材和群发任务；不同账号的数据相互隔离。</p>
    </div>
    '''
    if TELEGRAM_LOGIN_BOT_USERNAME and TELEGRAM_LOGIN_BOT_TOKEN:
        content += '''<div class="card"><h2>Telegram 快捷登录</h2>
        <p class="muted">也可以使用 Telegram 官方授权登录；首次使用会自动创建免费账号。</p>
        <script async src="https://telegram.org/js/telegram-widget.js?22"
          data-telegram-login="{{login_bot_username}}" data-size="large"
          data-auth-url="{{login_callback_url}}" data-request-access="write"></script></div>'''
        content += '''<details class="card details"><summary>平台管理员入口</summary>
        <form method="post"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
        <label>平台管理员密码</label><input type="password" name="admin_password" required autocomplete="current-password">
        <button type="submit">管理员登录</button></form></details>'''
        return page(content, login_bot_username=TELEGRAM_LOGIN_BOT_USERNAME,
                    login_callback_url=url_for("telegram_login_callback",_external=True))
    content += '''<details class="card details"><summary>平台管理员入口</summary>
    <form method="post"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <label>平台管理员密码</label><input type="password" name="admin_password" required autocomplete="current-password">
    <button type="submit">管理员登录</button></form></details>'''
    return page(content)


@app.route("/register", methods=["GET", "POST"])
def register():
    if not ALLOW_PUBLIC_REGISTRATION:
        abort(403)
    if session.get("authenticated"):
        return redirect(url_for("index"))
    if request.method == "POST":
        ip = request.remote_addr or "unknown"
        if registration_is_rate_limited(ip):
            abort(429)
        record_registration_attempt(ip)
        email = request.form.get("email", "").strip().lower()
        username = request.form.get("username", "").strip()
        password = request.form.get("password", "")
        confirm = request.form.get("password_confirm", "")
        if password != confirm:
            flash("两次输入的密码不一致。")
        else:
            try:
                user_id = create_local_user(email, password, username)
                session.clear()
                session["authenticated"] = True
                session["user_id"] = user_id
                session["auth_method"] = "local_password"
                session.permanent = True
                flash("注册成功，已自动登录。")
                return redirect(url_for("index"))
            except sqlite3.IntegrityError:
                flash("该邮箱已经注册，请直接登录。")
            except ValueError as exc:
                flash(str(exc))
    content = '''
    <div class="card"><h2>免费注册 TG管家账号</h2><form method="post">
    <input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
    <label>邮箱账号</label><input type="email" name="email" required autocomplete="email" placeholder="name@example.com">
    <label>显示名称（选填）</label><input name="username" maxlength="64" placeholder="你的名称">
    <label>设置密码（至少 6 位）</label><input type="password" name="password" minlength="6" required autocomplete="new-password">
    <label>确认密码</label><input type="password" name="password_confirm" minlength="6" required autocomplete="new-password">
    <button type="submit">创建免费账号</button> <a href="/login">返回登录</a></form>
    <p class="muted">当前免费版使用邮箱作为登录账号；暂不发送邮箱验证码。请使用你能长期访问的邮箱，并妥善保管密码。</p></div>
    '''
    return page(content)


@app.route("/account", methods=["GET", "POST"])
@login_required
def account():
    user_id = current_owner_id()
    if user_id == "legacy_admin":
        flash("当前使用旧版管理员密码登录；顾客账号请使用独立注册账号。")
        return redirect(url_for("index"))
    with db() as c:
        user = c.execute("SELECT * FROM user_accounts WHERE id=?", (user_id,)).fetchone()
    if not user:
        abort(404)
    if request.method == "POST":
        email = request.form.get("email", "").strip().lower()
        username = request.form.get("username", "").strip()[:64]
        current_password = request.form.get("current_password", "")
        new_password = request.form.get("new_password", "")
        confirm = request.form.get("password_confirm", "")
        if not email or len(email) > 254 or not re.fullmatch(r"[^\s@]+@[^\s@]+\.[^\s@]+", email):
            flash("邮箱格式无效。")
        elif new_password and len(new_password) < 6:
            flash("新密码至少需要 6 个字符。")
        elif new_password and len(new_password) > 1024:
            flash("新密码长度不能超过 1024 个字符。")
        elif new_password and new_password != confirm:
            flash("两次输入的新密码不一致。")
        elif user["password_hash"] and (email != (user["email"] or "") or new_password) and not verify_password(current_password, user["password_hash"]):
            flash("修改邮箱或密码前，请先输入当前密码。")
        else:
            try:
                with db() as c:
                    c.execute("UPDATE user_accounts SET email=?,username=?,password_hash=? WHERE id=?",
                        (email or None, username or user["username"], hash_password(new_password) if new_password else user["password_hash"], user_id))
                flash("账号资料已保存。")
                return redirect(url_for("account"))
            except sqlite3.IntegrityError:
                flash("该邮箱已被其他账号使用。")
    content = """<div class="page-intro"><div><span class="eyebrow">Account / 个人资料</span><h1>账号设置</h1><p>管理登录邮箱、显示名称和账号密码。</p></div></div>
    <div class="card"><div class="section-head"><div><h2>基本资料</h2><p>这些信息仅用于你的 TG管家账号。</p></div><span class="status-pill success">账号正常</span></div><form method="post"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><div class="field-grid"><div><label>邮箱账号</label><input type="email" name="email" value="{{user.email or ''}}" required></div><div><label>显示名称</label><input name="username" value="{{user.username or ''}}" maxlength="64"></div></div><hr><h2>修改密码</h2><p class="muted">如通过 Telegram 登录且尚未设置密码，可直接设置新密码。新密码至少 6 个字符。</p><div class="field-grid"><div><label>当前密码（首次设置可留空）</label><input type="password" name="current_password" autocomplete="current-password"></div><div><label>新密码（留空表示不修改）</label><input type="password" name="new_password" minlength="6" autocomplete="new-password"></div><div><label>确认新密码</label><input type="password" name="password_confirm" minlength="6" autocomplete="new-password"></div></div><button type="submit">保存账号设置</button></form></div>"""
    return page(content, user=user)


@app.get("/admin/users")
@login_required
def admin_users():
    require_admin()
    with db() as c:
        users = c.execute("SELECT u.*, (SELECT COUNT(*) FROM bots b WHERE b.owner_user_id=u.id) AS bot_count, (SELECT COUNT(*) FROM tasks t WHERE t.owner_user_id=u.id) AS task_count FROM user_accounts u ORDER BY u.created_at DESC").fetchall()
        counts = c.execute("SELECT COUNT(*) AS total, SUM(CASE WHEN status='active' THEN 1 ELSE 0 END) AS active FROM user_accounts").fetchone()
    content = """<div class="page-intro"><div><span class="eyebrow">Administration / 平台管理</span><h1>用户管理</h1><p>管理免费版用户、权限和账号状态；停用账号不会删除用户数据。</p></div></div>
    <div class="stats-grid"><div class="stat-card"><div class="stat-top">注册用户<span class="stat-icon">♙</span></div><div class="stat-value">{{counts.total or 0}}</div><div class="stat-note">平台注册账号总数</div></div><div class="stat-card"><div class="stat-top">正常账号<span class="stat-icon">✓</span></div><div class="stat-value">{{counts.active or 0}}</div><div class="stat-note">当前允许登录的账号</div></div></div>
    <div class="card"><div class="section-head"><div><h2>平台账号列表</h2><p>可以授予或撤销管理员权限、停用或恢复账号，以及重置密码。</p></div><span class="status-pill">{{users|length}} 个账号</span></div><div class="table-scroll"><table><thead><tr><th>账号</th><th>Telegram ID</th><th>角色</th><th>状态</th><th>机器人</th><th>任务</th><th>注册时间</th><th>操作</th></tr></thead><tbody>{% for u in users %}<tr><td><strong>{{u.username or '未设置'}}</strong><br><small class="muted">{{u.email or 'Telegram 登录账号'}}</small></td><td>{{u.telegram_user_id or '-'}}</td><td>{{'平台管理员' if u.role=='admin' else '普通用户'}}</td><td><span class="status-pill {% if u.status=='active' %}success{% else %}error{% endif %}">{{'正常' if u.status=='active' else '已停用'}}</span></td><td>{{u.bot_count}}</td><td>{{u.task_count}}</td><td>{{u.created_at}}</td><td>{% if u.role=='admin' %}<form method="post" action="/admin/users/{{u.id}}/demote"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button class="secondary">撤销管理员</button></form>{% else %}<form method="post" action="/admin/users/{{u.id}}/promote"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button>设为管理员</button></form>{% endif %}{% if u.status=='active' %}<form method="post" action="/admin/users/{{u.id}}/suspend"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button class="danger">停用</button></form>{% else %}<form method="post" action="/admin/users/{{u.id}}/activate"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button class="secondary">恢复</button></form>{% endif %}{% if u.email %}<form method="post" action="/admin/users/{{u.id}}/reset_password"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button class="secondary">重置密码</button></form>{% endif %}</td></tr>{% endfor %}</tbody></table></div></div>"""
    return page(content, users=users, counts=counts)


@app.post("/admin/users/<user_id>/<action>")
@login_required
def admin_user_action(user_id, action):
    require_admin()
    allowed = {"promote", "demote", "suspend", "activate", "reset_password"}
    if action not in allowed:
        abort(404)
    with db() as c:
        user = c.execute("SELECT * FROM user_accounts WHERE id=?", (user_id,)).fetchone()
        if not user:
            abort(404)
        if action in ("demote", "suspend"):
            if user_id == current_owner_id():
                flash("不能停用或撤销当前登录账号的管理员权限。")
                return redirect(url_for("admin_users"))
            if user["role"] == "admin" and user["status"] == "active":
                active_admins = c.execute("SELECT COUNT(*) FROM user_accounts WHERE role='admin' AND status='active'").fetchone()[0]
                if active_admins <= 1 and action == "demote":
                    flash("平台必须至少保留一名正常状态的管理员。")
                    return redirect(url_for("admin_users"))
                if active_admins <= 1 and action == "suspend":
                    flash("不能停用最后一名正常状态的管理员。")
                    return redirect(url_for("admin_users"))
        if action == "promote":
            c.execute("UPDATE user_accounts SET role='admin' WHERE id=?", (user_id,))
            flash("已授予平台管理员权限。")
        elif action == "demote":
            c.execute("UPDATE user_accounts SET role='user' WHERE id=?", (user_id,))
            flash("已撤销平台管理员权限。")
        elif action == "suspend":
            c.execute("UPDATE user_accounts SET status='suspended' WHERE id=?", (user_id,))
            flash("账号已停用；其数据和机器人配置均予以保留。")
        elif action == "activate":
            c.execute("UPDATE user_accounts SET status='active' WHERE id=?", (user_id,))
            flash("账号已恢复。")
        elif action == "reset_password":
            temporary = secrets.token_urlsafe(12)
            c.execute("UPDATE user_accounts SET password_hash=? WHERE id=?", (hash_password(temporary), user_id))
            flash("临时密码（仅显示本次）：" + temporary)
    return redirect(url_for("admin_users"))


@app.get("/auth/telegram/callback")
def telegram_login_callback():
    if not TELEGRAM_LOGIN_BOT_TOKEN or not TELEGRAM_LOGIN_BOT_USERNAME:
        abort(503)
    payload=request.args.to_dict(flat=True)
    ok,result=verify_telegram_login(payload)
    if not ok:
        logging.warning("Telegram login rejected: %s",result)
        abort(403)
    if not consume_telegram_login_hash(payload.get("hash")):
        logging.warning("Telegram login replay rejected")
        abort(403)
    with db() as c:
        user = c.execute("SELECT * FROM user_accounts WHERE telegram_user_id=?", (result,)).fetchone()
        if user and user["status"] != "active":
            abort(403)
        if not user:
            if not ALLOW_PUBLIC_REGISTRATION and result not in TELEGRAM_LOGIN_ADMIN_USER_IDS:
                abort(403)
            role = "admin" if result in TELEGRAM_LOGIN_ADMIN_USER_IDS else "user"
            c.execute("""INSERT INTO user_accounts(id,telegram_user_id,username,first_name,last_name,role,status,created_at,last_login_at)
                VALUES(?,?,?,?,?,?,'active',?,?)""",
                (result,result,payload.get("username"),payload.get("first_name"),payload.get("last_name"),role,now(),now()))
            user_id = result
        else:
            c.execute("""UPDATE user_accounts SET username=?,first_name=?,last_name=?,last_login_at=? WHERE id=?""",
                (payload.get("username"),payload.get("first_name"),payload.get("last_name"),now(),user["id"]))
            user_id = user["id"]
        # Keep the legacy Telegram users table populated for backward compatibility.
        c.execute("""INSERT INTO users(telegram_user_id,username,first_name,last_name,created_at,last_login_at)
            VALUES(?,?,?,?,?,?) ON CONFLICT(telegram_user_id) DO UPDATE SET
            username=excluded.username,first_name=excluded.first_name,last_name=excluded.last_name,
            last_login_at=excluded.last_login_at""",
            (result,payload.get("username"),payload.get("first_name"),payload.get("last_name"),now(),now()))
    session.clear()
    session["authenticated"] = True
    session["auth_method"] = "telegram"
    session["telegram_user_id"] = result
    session["user_id"] = user_id
    session.permanent = True
    return redirect(url_for("index"))

@app.post("/logout")
@login_required
def logout():
    session.clear()
    flash("已退出登录。")
    return redirect(url_for("login"))

@app.route("/")
@login_required
def index():
    bot_where, bot_params = owner_clause("bots.owner_user_id")
    task_where, task_params = owner_clause("owner_user_id")
    with db() as c:
        bots=c.execute(f"SELECT * FROM bots WHERE status<>'deleted' AND {bot_where} ORDER BY id DESC",bot_params).fetchall()
        chats=c.execute(f"""SELECT chats.*,bots.username AS bot_username FROM chats JOIN bots ON bots.id=chats.bot_id
            WHERE bots.status<>'deleted' AND chats.status<>'deleted' AND {bot_where} ORDER BY chats.id DESC""",bot_params).fetchall()
        tasks=c.execute(f"SELECT * FROM tasks WHERE {task_where} ORDER BY id DESC LIMIT 10",task_params).fetchall()
        task_stats=c.execute(f"""SELECT COUNT(*) AS total,
            SUM(CASE WHEN status IN ('running','scheduled') THEN 1 ELSE 0 END) AS active,
            SUM(CASE WHEN status='completed' THEN 1 ELSE 0 END) AS completed
            FROM tasks WHERE {task_where}""",task_params).fetchone()
    content="""
    <div class="page-intro"><div><span class="eyebrow">Overview / 工作台</span><h1>运营控制台</h1><p>集中管理 Telegram 机器人、群组和群发任务，实时掌握运营情况。</p></div><a class="btn" href="/broadcast">＋ 创建群发任务</a></div>
    <div class="stats-grid"><div class="stat-card"><div class="stat-top"><span>我的机器人</span><span class="stat-icon">◉</span></div><div class="stat-value">{{bots|length}}</div><div class="stat-note">已添加到当前账号</div></div><div class="stat-card"><div class="stat-top"><span>已发现群组</span><span class="stat-icon">♧</span></div><div class="stat-value">{{chats|length}}</div><div class="stat-note">机器人已识别的目标群组</div></div><div class="stat-card"><div class="stat-top"><span>执行中任务</span><span class="stat-icon">◷</span></div><div class="stat-value">{{task_stats.active or 0}}</div><div class="stat-note">正在发送或等待定时执行</div></div><div class="stat-card"><div class="stat-top"><span>累计群发任务</span><span class="stat-icon">▤</span></div><div class="stat-value">{{task_stats.total or 0}}</div><div class="stat-note">其中已完成 {{task_stats.completed or 0}} 个</div></div></div>
    <div class="card"><div class="section-head"><div><h2>快捷操作</h2><p>从常用操作开始管理你的 Telegram 社群。</p></div></div><div class="quick-actions"><a href="#bots">＋ 添加机器人</a><a href="/broadcast">↗ 创建群发</a><a href="/history">◷ 查看发送记录</a><a href="/account">⚙ 账号设置</a></div></div>
    <div class="card" id="bots"><div class="section-head"><div><h2>我的机器人</h2><p>添加成功后会自动监听。请将机器人邀请到目标群组。</p></div><span class="status-pill">{{bots|length}} 个机器人</span></div><form method="post" action="/bots/add" data-bot-add><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><div class="field-grid"><div><label>Telegram Bot Token</label><input name="token" type="password" autocomplete="new-password" required placeholder="粘贴从 BotFather 获取的新 Token"></div><div style="display:flex;align-items:flex-end"><button type="submit">验证并添加机器人</button></div></div><p class="muted">新 Token 只有通过 Telegram 验证后才会加密保存；此输入框不会回显已保存 Token。</p></form><div class="helper-box">当前显示的 {{bots|length}} 个机器人和 {{chats|length}} 个群组是数据库中已保存的数据。添加新机器人失败只会拒绝本次 Token，不会删除已有机器人或群组。机器人“已保存”不等于 Telegram 实时连接正常，请查看下方连接状态。</div>
    {% if bots %}<div class="table-scroll"><table><thead><tr><th>机器人</th><th>用户名</th><th>状态</th><th>操作</th></tr></thead><tbody>{% for b in bots %}<tr><td><strong>{{b.first_name or 'Telegram Bot'}}</strong></td><td>@{{b.username}}</td><td><span class="status-pill {% if b.last_api_status=='connected' %}success{% elif b.last_api_status=='error' or b.status=='invalid_token' %}error{% else %}warning{% endif %}">{{'Token 失效' if b.status=='invalid_token' else ('已停用' if b.status!='active' else ('连接正常' if b.last_api_status=='connected' else ('连接异常' if b.last_api_status=='error' else '已保存，等待连接')) )}}</span>{% if b.last_api_error %}<br><small class="muted">{{b.last_api_error}}</small>{% endif %}</td><td><button type="button" class="secondary" data-token-bot="{{b.id}}">查看 Token</button><a class="btn secondary" href="/bots/{{b.id}}/profile">导出配置</a>{% if b.status != 'disabled' %}<form method="post" action="/bots/{{b.id}}/delete" style="display:inline" onsubmit="return confirm('确认【只删除 Token，保留记录】？将清除凭据、停止监听和未发送任务，把机器人标记为已停用；机器人、群组、素材和历史仍在只读记录中可查。');"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><input type="hidden" name="delete_mode" value="token"><button class="secondary">只删除 Token，保留记录</button></form>{% endif %}<form method="post" action="/bots/{{b.id}}/delete" style="display:inline" onsubmit="return confirm('确认【删除机器人和所有专属记录】？将永久清除凭据、机器人群组关系、采集来源、素材、按钮动作及该机器人专属投递记录；多机器人共享任务仅移除当前机器人目标。此操作不可恢复！');"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><input type="hidden" name="delete_mode" value="all"><input type="hidden" name="confirm_all" value="yes"><button class="danger">删除机器人和所有专属记录</button></form></td></tr>{% endfor %}</tbody></table></div>{% else %}<div class="helper-box">还没有添加机器人。先在 Telegram 中通过 @BotFather 创建机器人，再把 Token 填入上方即可。</div>{% endif %}</div>
    {% set abnormal_chats = chats|selectattr('status', 'in', ['removed', 'no_permission'])|list %}<div class="card" data-group-status><div class="section-head"><div><h2>已发现群组</h2><p>机器人加入群组后，系统会自动识别群组。</p></div><div><span class="status-pill">{{chats|length}} 个群组</span>{% if abnormal_chats %}<form method="post" action="/chats/remove-abnormal" style="display:inline;margin-left:8px" onsubmit="return confirm('确认一键清除当前账号下的全部 {{abnormal_chats|length}} 个异常群？正常群、其他机器人关联及发送历史将继续保留。');"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button class="danger">一键清除全部异常群（{{abnormal_chats|length}}）</button></form>{% endif %}</div></div>{% if chats %}<div class="table-scroll"><table><thead><tr><th>群组名称</th><th>所属机器人</th><th>状态</th></tr></thead><tbody>{% for g in chats %}<tr><td><strong>{{g.title}}</strong><br><small class="muted">{{g.chat_id}}</small></td><td>@{{g.bot_username}}</td><td><span class="status-pill {% if g.status in ['removed','no_permission'] %}error{% elif g.status=='active' %}success{% endif %}">{{g.status|status_zh}}</span>{% if g.status in ['removed','no_permission'] %}<br><small class="muted">最近异常时间：{{g.last_seen or '未知'}}</small><form method="post" action="/bots/{{g.bot_id}}/chats/{{g.id}}/remove" onsubmit="return confirm('确认删除此异常群（{{g.title}}）？只清理当前机器人与该群的关联，发送历史保留。');"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button class="danger" aria-label="删除异常群">删除此异常群</button></form>{% endif %}</td></tr>{% endfor %}</tbody></table></div>{% else %}<div class="helper-box">还没有发现群组。请把已添加的机器人邀请到目标群组，确保机器人拥有读取消息和发送消息的权限。</div>{% endif %}</div>
    <div class="card"><div class="section-head"><div><h2>最近群发任务</h2><p>查看任务状态，必要时暂停、恢复或取消发送。</p></div><a href="/history">查看全部记录 →</a></div>{% if tasks %}<div class="table-scroll"><table><thead><tr><th>任务</th><th>状态</th><th>创建时间</th><th>执行结果</th><th>操作</th></tr></thead><tbody>{% for t in tasks %}<tr><td><strong>#{{t.id}}</strong></td><td><span class="status-pill {% if t.status=='completed' %}success{% elif t.status in ['failed','cancelled'] %}error{% elif t.status in ['paused','unknown'] %}warning{% endif %}">{{t.status|status_zh}}</span></td><td>{{t.created_at}}</td><td>{{t.result or '—'}}</td><td><a href="/tasks/{{t.id}}">详情</a>{% if t.status in ['running','scheduled'] %}<form method="post" action="/tasks/{{t.id}}/pause"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button class="secondary">暂停</button></form>{% endif %}{% if t.status=='paused' %}<form method="post" action="/tasks/{{t.id}}/resume"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button>恢复</button></form>{% endif %}{% if t.status in ['running','scheduled','paused','unknown'] %}<form method="post" action="/tasks/{{t.id}}/cancel"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button class="danger">取消</button></form>{% endif %}</td></tr>{% endfor %}</tbody></table></div>{% else %}<div class="helper-box">暂时还没有群发任务。添加机器人并选择目标群组后，即可创建第一条群发任务。</div>{% endif %}</div>
    """
    return page(content,bots=bots,chats=chats,tasks=tasks,task_stats=task_stats)

@app.post("/bots/add")
@login_required
def add_bot():
    token=request.form.get("token","").strip()
    try:
        if not re.fullmatch(r"[0-9]+:[A-Za-z0-9_-]{20,}", token) or len(token) > 256:
            flash("Token 格式不正确，请复制 BotFather 提供的完整 Token。")
            return redirect(url_for("index"))
        me=api(token,"getMe",timeout=10)
        verified_at=now()
        with db() as c:
            c.execute("BEGIN IMMEDIATE")
            limit_row = c.execute("SELECT value FROM settings WHERE key='user_bot_limit'").fetchone()
            bot_limit = int(limit_row["value"]) if limit_row else 0
            bot_count = c.execute("SELECT COUNT(*) FROM bots WHERE owner_user_id=? AND status<>'deleted'", (current_owner_id(),)).fetchone()[0]
            if bot_limit and bot_count >= bot_limit:
                flash(f"最多可添加 {bot_limit} 个机器人，当前已达到上限。")
                return redirect(url_for("index"))
            existing=c.execute("SELECT id, status, owner_user_id FROM bots WHERE telegram_id=?", (me["id"],)).fetchall()
            if any(row["status"] not in ("deleted", "disabled") for row in existing):
                flash("这个 Telegram Bot 已经被本平台账号添加过。")
                return redirect(url_for("index"))
            if any((thread := polling_threads.get(row["id"])) is not None and thread.is_alive() for row in existing):
                flash("旧机器人的监听正在退出，请稍后重新添加。")
                return redirect(url_for("index"))
            for row in existing:
                if row["status"] == "disabled" and row["owner_user_id"] == current_owner_id():
                    c.execute("UPDATE bots SET status='deleted',token='deleted:' || id WHERE id=?", (row["id"],))
            c.execute("INSERT INTO bots(token,telegram_id,username,first_name,token_encryption_version,status,created_at,owner_user_id,last_api_status,last_api_ok_at) VALUES(?,?,?,?,?,?,?,?,?,?)",
                      (encrypt_token(token),me["id"],me.get("username",""),me.get("first_name",""),1,"active",verified_at,current_owner_id(),"connected",verified_at))
        with db() as c:
            new_bot = c.execute("SELECT id FROM bots WHERE telegram_id=? AND owner_user_id=? AND status='active'", (me["id"], current_owner_id())).fetchone()
            previous_chats = c.execute("""SELECT DISTINCT ch.chat_id FROM chats ch
                JOIN bots b ON b.id=ch.bot_id
                WHERE b.telegram_id=? AND b.owner_user_id=? AND b.status='deleted'
                ORDER BY ch.chat_id""", (me["id"], current_owner_id())).fetchall()
        start_pollers()
        recovered = 0
        if new_bot:
            for previous in previous_chats:
                try:
                    membership = api(token, "getChatMember", {"chat_id": previous["chat_id"], "user_id": me["id"]}, timeout=10)
                    member_status = membership.get("status")
                    restricted_can_send = member_status == "restricted" and membership.get("is_member") and membership.get("can_send_messages")
                    if member_status not in ("member", "administrator", "creator") and not restricted_can_send:
                        continue
                    chat = api(token, "getChat", {"chat_id": previous["chat_id"]}, timeout=10)
                    if member_status == "member" and (chat.get("permissions") or {}).get("can_send_messages") is False:
                        continue
                    remember_chat(new_bot["id"], chat)
                    recovered += 1
                except (TelegramAPIError, requests.RequestException):
                    continue
        flash(f"已添加 @{me.get('username')}，系统会自动监听，已恢复 {recovered} 个群组。")
    except requests.Timeout:
        flash("Telegram 验证超时（api.telegram.org 在 10 秒内未响应）；本次 Token 未保存，已有机器人和群组不会受影响。")
    except requests.exceptions.ConnectionError:
        flash("无法连接 Telegram API（请检查容器 DNS、出站 HTTPS/443 和服务器防火墙）；本次 Token 未保存，已有机器人和群组不会受影响。")
    except TelegramAPIError:
        flash("Telegram 拒绝验证，请检查 Token 是否有效；Token 未保存。")
    except sqlite3.IntegrityError:
        flash("这个 Bot 已经添加过。")
    except Exception as e:
        logging.warning("Bot add failed: %s", type(e).__name__)
        flash("添加失败，请检查 Token、网络连接及 Telegram API 状态。")
    return redirect(url_for("index"))

@app.post("/bots/<int:bot_id>/poll")
@login_required
def poll_start(bot_id):
    where, params = owner_clause("owner_user_id")
    with db() as c:
        b=c.execute(f"SELECT * FROM bots WHERE id=? AND {where}",(bot_id,*params)).fetchone()
    if not b: abort(404)
    if b["status"] != "active":
        flash("该机器人当前不可用，请检查 Token 或重新添加机器人。")
        return redirect(url_for("index"))
    else:
        start_bot_poller(bot_id, b["token"])
        flash("已启动群组更新监听。")
    return redirect(url_for("index"))




def _cleanup_abnormal_chat_row(c, bot_id, chat_key, chat_id, affected_tasks):
    c.execute("UPDATE chats SET status='deleted',last_seen=? WHERE id=?", (now(), chat_key))
    c.execute("UPDATE collection_sources SET enabled=0,status_text='来源未启用' WHERE bot_id=? AND chat_id=?", (bot_id, chat_id))
    rows = c.execute(
        "SELECT DISTINCT task_id FROM delivery_jobs WHERE bot_id=? AND chat_id=? AND status IN ('pending','paused')",
        (bot_id, chat_id),
    ).fetchall()
    for r in rows:
        affected_tasks.add(r[0])
    c.execute(
        """UPDATE delivery_jobs SET status='cancelled',last_error='异常群组已手动清理',updated_at=?
           WHERE bot_id=? AND chat_id=? AND status IN ('pending','paused')""",
        (now(), bot_id, chat_id),
    )
    for table in ("join_auto_sends", "task_join_auto_sends"):
        c.execute(
            f"UPDATE {table} SET status='cancelled',last_error='异常群组已手动清理',updated_at=? "
            f"WHERE bot_id=? AND chat_id=? AND status IN ('pending','paused')",
            (now(), bot_id, chat_id),
        )


@app.post("/bots/<int:bot_id>/chats/<int:chat_key>/remove")
@login_required
def remove_chat(bot_id, chat_key):
    affected_tasks = set()
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        row = c.execute("""SELECT ch.* FROM chats ch JOIN bots b ON b.id=ch.bot_id
            WHERE ch.id=? AND ch.bot_id=? AND b.owner_user_id=?""",
            (chat_key, bot_id, current_owner_id())).fetchone()
        if not row:
            abort(404)
        if row["status"] not in ("removed", "no_permission"):
            abort(400)
        _cleanup_abnormal_chat_row(c, bot_id, chat_key, row["chat_id"], affected_tasks)
    for tid in affected_tasks:
        update_task_summary(tid)
    flash("异常群组已移除，发送历史已保留。")
    return redirect(url_for("index"))


@app.post("/chats/remove-abnormal")
@login_required
def remove_all_abnormal_chats():
    owner = current_owner_id()
    affected_tasks = set()
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        rows = c.execute(
            """SELECT ch.id, ch.bot_id, ch.chat_id FROM chats ch
               JOIN bots b ON b.id=ch.bot_id
               WHERE b.owner_user_id=? AND b.status<>'deleted'
               AND ch.status IN ('removed','no_permission')""",
            (owner,),
        ).fetchall()
        for r in rows:
            _cleanup_abnormal_chat_row(c, r["bot_id"], r["id"], r["chat_id"], affected_tasks)
    for tid in affected_tasks:
        update_task_summary(tid)
    flash(f"已一键清除 {len(rows)} 个异常群组，正常群及历史投递已保留。")
    return redirect(url_for("index"))


@app.post("/bots/<int:bot_id>/delete")
@login_required
def delete_bot(bot_id):
    delete_mode = request.form.get("delete_mode", "token")
    if delete_mode not in ("token", "all"):
        abort(400)
    if delete_mode == "all" and request.form.get("confirm_all") != "yes":
        flash("删除机器人和所有专属记录需要确认。")
        return redirect(url_for("index"))
    where, params = owner_clause("owner_user_id")
    # Stop polling thread first before entering DB transaction
    event = stop_events.get(bot_id)
    if event:
        event.set()
    thread = polling_threads.get(bot_id)
    if thread and thread.is_alive() and thread is not threading.current_thread():
        thread.join(timeout=1.5)
    with db() as c:
        c.execute("BEGIN IMMEDIATE")
        bot = c.execute(f"SELECT id,status FROM bots WHERE id=? AND {where}", (bot_id, *params)).fetchone()
        if not bot or (bot["status"] == "deleted" and delete_mode == "token"):
            abort(404)
        sending = c.execute(
            "SELECT (SELECT COUNT(*) FROM delivery_jobs WHERE bot_id=? AND status='sending') + "
            "(SELECT COUNT(*) FROM task_join_auto_sends WHERE bot_id=? AND status='sending') + "
            "(SELECT COUNT(*) FROM join_auto_sends WHERE bot_id=? AND status='sending')",
            (bot_id, bot_id, bot_id),
        ).fetchone()[0]
        if sending:
            flash("该机器人仍有正在发送的群组，请等待当前发送完成后再删除。")
            return redirect(url_for("index"))
        affected_tasks = {row[0] for row in c.execute(
            "SELECT DISTINCT task_id FROM delivery_jobs WHERE bot_id=? AND status IN ('pending','paused','unknown')", (bot_id,)
        ).fetchall()}
        # Stop unknown deliveries and leave explicit status/reason before deletion
        c.execute("""UPDATE delivery_jobs SET status='cancelled',updated_at=?,
            last_error=COALESCE(NULLIF(last_error,'' ) || '；','') || '删除机器人时停止处理，发送结果未确认'
            WHERE bot_id=? AND status='unknown'""", (now(), bot_id))
        c.execute("""UPDATE message_receipts SET status='unknown'
            WHERE status='sending' AND job_id IN (SELECT id FROM delivery_jobs WHERE bot_id=?)""", (bot_id,))
        c.execute("UPDATE delivery_jobs SET status='failed',last_error='机器人配置已删除，未发送内容已停止',updated_at=? WHERE bot_id=? AND status IN ('pending','paused')",
                  (now(), bot_id))
        c.execute("UPDATE task_join_auto_sends SET status='failed',last_error='机器人配置已删除',updated_at=? WHERE bot_id=? AND status IN ('pending','paused')",
                  (now(), bot_id))
        c.execute("UPDATE join_auto_sends SET status='failed',last_error='机器人配置已删除',updated_at=? WHERE bot_id=? AND status IN ('pending','paused')",
                  (now(), bot_id))
        c.execute("UPDATE collection_sources SET enabled=0,status_text='来源未启用' WHERE bot_id=?", (bot_id,))
        active_series = c.execute(f"SELECT id,config_json FROM recurring_series WHERE status IN ('active','paused') AND {where}", params).fetchall()
        for series in active_series:
            try:
                config = json.loads(series["config_json"] or "{}")
            except (TypeError, ValueError):
                continue
            old_bot_ids = [str(value) for value in config.get("bot_ids", [])]
            if str(bot_id) not in old_bot_ids:
                continue
            config["bot_ids"] = [value for value in old_bot_ids if value != str(bot_id)]
            config["chat_targets"] = [key for key in config.get("chat_targets", []) if str(key).split(":", 1)[0] != str(bot_id)]
            if not config["bot_ids"] or not config["chat_targets"]:
                c.execute("UPDATE recurring_series SET status='cancelled',updated_at=? WHERE id=?", (now(), series["id"]))
                c.execute("UPDATE tasks SET status='cancelled',result='机器人已删除，循环任务已停止' WHERE series_id=? AND status IN ('running','scheduled','paused')",
                          (series["id"],))
                c.execute("UPDATE delivery_jobs SET status='cancelled',updated_at=? WHERE task_id IN (SELECT id FROM tasks WHERE series_id=?) AND status IN ('pending','paused')",
                          (now(), series["id"]))
            else:
                c.execute("UPDATE recurring_series SET config_json=?,updated_at=? WHERE id=?",
                          (json.dumps(config, ensure_ascii=False), now(), series["id"]))
        if delete_mode == "token":
            # Mode 1: Only clear Token & stop bot; keep bot, chats, materials, and history readable in read-only state
            c.execute("UPDATE chats SET status='deleted',last_seen=? WHERE bot_id=?", (now(), bot_id))
            c.execute(
                "UPDATE bots SET lifecycle=lifecycle+1,status='deleted',token='deleted:' || id,"
                "last_api_status='error',last_api_error='用户已删除机器人配置' WHERE id=?",
                (bot_id,),
            )
        else:
            # Mode 2: Delete bot and all exclusive records; strip bot from multi-bot shared tasks
            bot_jobs = [row[0] for row in c.execute("SELECT id FROM delivery_jobs WHERE bot_id=?", (bot_id,))]
            for job_id in bot_jobs:
                c.execute("DELETE FROM message_receipts WHERE job_id=?", (job_id,))
                c.execute("DELETE FROM resolutions WHERE job_id=?", (job_id,))
            c.execute("DELETE FROM material_versions WHERE material_id IN (SELECT id FROM materials WHERE bot_id=?)", (bot_id,))
            for table in ("delivery_jobs", "task_join_auto_sends", "join_auto_sends",
                          "chats", "media_assets", "collection_sources", "materials",
                          "imports", "button_actions", "button_events", "credential_audit"):
                c.execute(f"DELETE FROM {table} WHERE bot_id=?", (bot_id,))
            owned_tasks = c.execute(f"SELECT id,bot_ids,chat_targets,media_assets FROM tasks WHERE {where}", params).fetchall()
            for task in owned_tasks:
                selected = json.loads(task["bot_ids"] or "[]")
                if str(bot_id) not in {str(value) for value in selected}:
                    continue
                remaining = [value for value in selected if str(value) != str(bot_id)]
                if remaining:
                    targets = [key for key in json.loads(task["chat_targets"] or "[]")
                               if str(key).split(":", 1)[0] != str(bot_id)]
                    assets = json.loads(task["media_assets"] or "{}")
                    assets.pop(str(bot_id), None)
                    c.execute("UPDATE tasks SET bot_ids=?,chat_targets=?,media_assets=? WHERE id=?",
                              (json.dumps(remaining), json.dumps(targets), json.dumps(assets), task["id"]))
                    affected_tasks.add(task["id"])
                else:
                    c.execute("DELETE FROM message_receipts WHERE job_id IN (SELECT id FROM delivery_jobs WHERE task_id=?)", (task["id"],))
                    c.execute("DELETE FROM resolutions WHERE job_id IN (SELECT id FROM delivery_jobs WHERE task_id=?)", (task["id"],))
                    c.execute("DELETE FROM delivery_jobs WHERE task_id=?", (task["id"],))
                    c.execute("DELETE FROM task_join_auto_sends WHERE task_id=?", (task["id"],))
                    c.execute("DELETE FROM task_versions WHERE task_id=?", (task["id"],))
                    c.execute("DELETE FROM tasks WHERE id=?", (task["id"],))
                    affected_tasks.discard(task["id"])
            c.execute("DELETE FROM bots WHERE id=?", (bot_id,))
        for task_id in affected_tasks:
            # Update summary inside the same transaction
            current_task = c.execute("SELECT status,series_id,semantics FROM tasks WHERE id=?", (task_id,)).fetchone()
            if not current_task or current_task["status"] == "cancelled":
                continue
            rows = c.execute("SELECT status, COUNT(*) AS n FROM delivery_jobs WHERE task_id=? GROUP BY status", (task_id,)).fetchall()
            counts = {r["status"]: r["n"] for r in rows}
            total = sum(counts.values())
            sent = counts.get("sent", 0)
            failed = counts.get("failed", 0)
            unknown = counts.get("unknown", 0)
            cancelled = counts.get("cancelled", 0)
            pending = counts.get("pending", 0) + counts.get("sending", 0)
            paused_cnt = counts.get("paused", 0)
            if pending:
                st = "running"
            elif paused_cnt:
                st = "paused"
            elif unknown:
                st = "unknown"
            elif cancelled and (sent or c.execute("SELECT COALESCE(SUM(success_count),0) FROM delivery_jobs WHERE task_id=?", (task_id,)).fetchone()[0] > 0):
                st = "partial"
            elif cancelled and not sent:
                st = "cancelled"
            elif failed and sent:
                st = "partial"
            elif failed:
                st = "failed"
            else:
                st = "completed"
            confirmed = c.execute("SELECT COALESCE(SUM(success_count),0) FROM delivery_jobs WHERE task_id=?", (task_id,)).fetchone()[0] if current_task["semantics"] == "per_target" else sent
            res_text = f"总目标 {total}；成功 {confirmed}；失败 {failed}；结果未知 {unknown}；已停止 {cancelled}；待处理 {pending}"
            c.execute("UPDATE tasks SET status=?,result=? WHERE id=?", (st, res_text, task_id))
    flash("机器人及专属记录已删除。" if delete_mode == "all" else "Token 已清除，群组和素材保留，历史任务和发送日志保留。")
    return redirect(url_for("index"))


@app.post("/tasks/<int:task_id>/<action>")
@login_required
def task_action(task_id, action):
    actions={"pause":pause_task,"resume":resume_task,"cancel":cancel_task,"retry_failed":retry_failed_jobs}
    if action not in actions:
        abort(404)
    where, params = owner_clause("owner_user_id")
    with db() as c:
        owned = c.execute(f"SELECT id FROM tasks WHERE id=? AND {where}",(task_id,*params)).fetchone()
    if not owned:
        abort(404)
    ok,message=actions[action](task_id)
    flash(message)
    return redirect(url_for("index"))


def parse_schedule_timestamp(raw_value, tz_offset_minutes="0"):
    if not raw_value:
        return int(time.time())
    try:
        local_dt = datetime.fromisoformat(raw_value)
        offset = int(tz_offset_minutes)
    except (TypeError, ValueError) as exc:
        raise ValueError("定时执行时间格式无效") from exc
    if local_dt.tzinfo is not None:
        timestamp = int(local_dt.timestamp())
    else:
        if abs(offset) > 14 * 60:
            raise ValueError("浏览器时区偏移无效")
        utc_dt = (local_dt + timedelta(minutes=offset)).replace(tzinfo=timezone.utc)
        timestamp = int(utc_dt.timestamp())
    if timestamp <= int(time.time()):
        raise ValueError("定时执行时间必须晚于当前时间")
    return timestamp


@app.route("/broadcast",methods=["GET","POST"])
@login_required
def broadcast():
    if request.method == "POST":
        bot_ids = request.form.getlist("bot_ids")
        chat_keys = request.form.getlist("chat_keys")
        content_modes = [x for x in ("text", "photo", "video") if x in request.form.getlist("content_modes")]
        body = request.form.get("body", "").strip() if "text" in content_modes else ""
        rotation_messages = parse_rotation_messages(request.form.get("rotation_messages", "").strip())
        media_assets_by_bot = {}
        repeat_enabled = request.form.get("repeat_enabled") == "on"
        repeat_duration_seconds = 0
        repeat_max_runs = 0
        sender_mode = request.form.get("sender_mode", "hide")
        try:
            scheduled_epoch = parse_schedule_timestamp(request.form.get("scheduled_at", ""), request.form.get("tz_offset_minutes", "0"))
            send_gap_seconds = parse_send_gap_seconds(request.form.get("send_gap_seconds", platform_send_gap_seconds()))
            buttons = parse_buttons(request.form.get("buttons", ""))
            if isinstance(buttons, dict):
                raise ValueError("新群发任务仅支持内联按钮。")
            auto_join_enabled = request.form.get("auto_join_enabled") == "on"
            if repeat_enabled:
                duration_unit = request.form.get("repeat_duration_unit", "none")
                duration_value = int(request.form.get("repeat_duration_value", "0") or 0)
                repeat_max_runs = int(request.form.get("repeat_max_runs", "0") or 0)
                unit_seconds = {"none": 0, "minutes": 60, "hours": 3600, "days": 86400}
                if duration_unit not in unit_seconds:
                    raise ValueError("定时停止单位无效")
                if duration_unit == "none":
                    if duration_value:
                        raise ValueError("未选择定时单位时，请清空停止时长")
                elif not 1 <= duration_value <= 36500:
                    raise ValueError("定时停止时长必须为 1 至 36500")
                else:
                    repeat_duration_seconds = duration_value * unit_seconds[duration_unit]
                if not 0 <= repeat_max_runs <= 10000:
                    raise ValueError("循环轮数不能超过 10000；留空表示不限制")
            else:
                repeat_duration_seconds = 0
                repeat_max_runs = 0
            if not bot_ids or not chat_keys or not content_modes:
                raise ValueError("请至少选择一个机器人、一个群组和一种发送内容。");
            if "text" in content_modes and not body and not rotation_messages:
                raise ValueError("已勾选文字发送，请填写文字内容。")
            if "text" not in content_modes and body:
                body = ""
            if rotation_messages and content_modes != ["text"]:
                raise ValueError("消息轮换仅支持纯文字群发，请只勾选文字。");
            if len(rotation_messages) > 20 or any(len(item) > 4096 for item in rotation_messages):
                raise ValueError("每个任务最多 20 条轮换消息，单条不超过 4096 字符。")
            if rotation_messages and body:
                raise ValueError("使用轮换消息时，请将普通正文留空。")
            ad_mode = forced_ad_mode()
            ad_text_snapshot = setting("ad_text") if ad_mode in ("TEXT_ONLY", "BOTH") else ""
            text_candidates = rotation_messages if rotation_messages else ([body] if "text" in content_modes else [])
            if any(len(item + (("\n\n" + ad_text_snapshot) if ad_text_snapshot else "")) > 4096 for item in text_candidates):
                raise ValueError("文字消息与平台广告合计不能超过 4096 字符。")
            if "text" not in content_modes and ad_text_snapshot and len(ad_text_snapshot) > 1024:
                raise ValueError("平台广告文字超过 Telegram 媒体说明文字限制（1024 字符）。")
            where, params = owner_clause("owner_user_id")
            with db() as c:
                owned_bots = c.execute(f"SELECT id,token,username,first_name FROM bots WHERE status='active' AND {where}", params).fetchall()
                owned_bot_ids = {str(row["id"]): row for row in owned_bots}
                if any(str(bid) not in owned_bot_ids for bid in bot_ids):
                    raise ValueError("所选机器人不存在或不属于当前账号。")
                for bid in bot_ids:
                    selected_ids = request.form.getlist(f"media_assets_{bid}")
                    selected = load_selected_media_assets(c, int(bid), selected_ids)
                    media_assets_by_bot[str(bid)] = selected
                    for media_type in ("photo", "video"):
                        if media_type in content_modes and not any(x["type"] == media_type for x in selected):
                            raise ValueError(f"机器人 ID {bid} 尚未选择要发送的{'图片' if media_type == 'photo' else '视频'}。")
                targets = []
                for key in chat_keys:
                    bid, cid = map(int, key.split(":"))
                    if str(bid) not in bot_ids:
                        continue
                    bot = owned_bot_ids.get(str(bid))
                    chat = c.execute("SELECT title FROM chats WHERE bot_id=? AND chat_id=? AND status='active'", (bid, cid)).fetchone()
                    if bot and chat:
                        targets.append((bid, cid, chat["title"]))
            if not targets:
                raise ValueError("所选机器人没有可发送的有效群组。")
            if "photo" in content_modes or "video" in content_modes:
                if not any(media_assets_by_bot.values()):
                    raise ValueError("请从 Telegram 媒体库选择图片或视频。")
            with db() as c:
                task_status = "scheduled" if scheduled_epoch > int(time.time()) else "running"
                cur = c.execute("""INSERT INTO tasks
                    (bot_ids,chat_targets,body,buttons,ad_mode,ad_text,ad_button_text,ad_url,status,created_at,
                     media_path,media_type,scheduled_at,rotation_messages,content_modes,media_assets,auto_join_enabled,owner_user_id,send_gap_seconds,sender_mode)
                    VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                    (json.dumps(bot_ids), json.dumps(chat_keys), body, json.dumps(buttons, ensure_ascii=False),
                     ad_mode, ad_text_snapshot, setting("ad_button_text"), setting("ad_url"), task_status, now(),
                     None, None, scheduled_epoch, json.dumps(rotation_messages, ensure_ascii=False),
                     json.dumps(content_modes), json.dumps(media_assets_by_bot), int(auto_join_enabled), current_owner_id(), send_gap_seconds, sender_mode))
                task_id = cur.lastrowid
                bind_prompt_actions(c, request.form.get("buttons", ""), bot_ids)
                for sequence_no, (bid, cid, title) in enumerate(targets):
                    c.execute("""INSERT OR IGNORE INTO delivery_jobs
                        (task_id,bot_id,chat_id,chat_title,sequence_no,status,attempts,next_attempt_at,created_at,updated_at)
                        VALUES(?,?,?,?,?,'pending',0,?,?,?)""",
                        (task_id, bid, cid, title, sequence_no, scheduled_epoch, now(), now()))
                c.execute("UPDATE tasks SET status=?,result=? WHERE id=?",
                          (task_status, f"{'已预约定时发送' if task_status == 'scheduled' else '已加入发送队列'}，共 {len(targets)} 个目标。", task_id))
                if request.form.get('semantics') == 'per_target':
                    c.execute("UPDATE tasks SET semantics='per_target',max_success=?,stop_after_seconds=? WHERE id=?",
                              (repeat_max_runs if repeat_enabled else 1, repeat_duration_seconds, task_id))
                if repeat_enabled and request.form.get('semantics') != 'per_target':
                    recurrence_config = {"bot_ids": bot_ids, "chat_targets": chat_keys, "body": body, "buttons": buttons,
                        "ad_mode": ad_mode, "ad_text": ad_text_snapshot, "ad_button_text": setting("ad_button_text"),
                        "ad_url": setting("ad_url"), "media_path": None, "media_type": None,
                        "rotation_messages": rotation_messages, "content_modes": content_modes,
                        "media_assets": media_assets_by_bot, "auto_join_enabled": auto_join_enabled,
                        "send_gap_seconds": send_gap_seconds, "sender_mode": sender_mode}
                    c.execute("""INSERT INTO recurring_series
                        (config_json,interval_seconds,max_runs,runs_created,next_run_at,last_task_id,status,created_at,updated_at,owner_user_id,loop_mode,stop_after_seconds)
                        VALUES(?,0,?,1,?,?,'active',?,?,?,'continuous',?)""",
                        (json.dumps(recurrence_config, ensure_ascii=False), repeat_max_runs, scheduled_epoch,
                         task_id, now(), now(), current_owner_id(), repeat_duration_seconds))
                    series_id = c.execute("SELECT last_insert_rowid() AS id").fetchone()["id"]
                    c.execute("UPDATE tasks SET series_id=? WHERE id=?", (series_id, task_id))
            start_delivery_worker()
            flash(f"任务 #{task_id} 已创建：{len(targets)} 个目标；群组发送间隔 {send_gap_seconds:g} 秒；内容类型：{'、'.join({'text':'文字','photo':'图片','video':'视频'}[x] for x in content_modes)}。")
            return redirect(url_for("index"))
        except Exception as exc:
            logging.warning("Broadcast creation failed: %s", type(exc).__name__)
            flash(str(exc) if isinstance(exc, ValueError) else "创建失败，请检查输入内容和目标群组。")
            return redirect(url_for("broadcast"))

    template_config = {}
    template_id = request.args.get("template_id", "")
    where, params = owner_clause("owner_user_id")
    bot_where, bot_params = owner_clause("bots.owner_user_id")
    with db() as c:
        bots = c.execute(f"SELECT * FROM bots WHERE status='active' AND {where} ORDER BY id", params).fetchall()
        chats = c.execute(f"""SELECT chats.*,bots.username AS bot_username FROM chats JOIN bots ON bots.id=chats.bot_id
            WHERE bots.status='active' AND chats.status='active' AND {bot_where} ORDER BY bots.id,chats.title""", bot_params).fetchall()
        templates = c.execute(f"SELECT * FROM task_templates WHERE {where} ORDER BY id DESC LIMIT 50", params).fetchall()
        media_assets_by_bot = {}
        for bot in bots:
            media_assets_by_bot[bot["id"]] = c.execute("SELECT * FROM media_assets WHERE bot_id=? ORDER BY id DESC LIMIT 100", (bot["id"],)).fetchall()
        if template_id:
            if template_id == "latest":
                row = c.execute(f"SELECT config_json FROM task_templates WHERE {where} ORDER BY id DESC LIMIT 1", params).fetchone()
            else:
                try: parsed_template_id = int(template_id)
                except (TypeError, ValueError): parsed_template_id = -1
                row = c.execute(f"SELECT config_json FROM task_templates WHERE id=? AND {where}",(parsed_template_id,*params)).fetchone()
            if row:
                try: template_config = json.loads(row["config_json"])
                except (TypeError, ValueError, json.JSONDecodeError): template_config = {}
    rotation_text = "\n---轮换消息---\n".join(template_config.get("rotation_messages", []))
    button_lines = []
    template_buttons=template_config.get("buttons", [])
    if isinstance(template_buttons, dict):
        flash("旧模板的回复键盘未载入。需要按钮时，请添加内联按钮。")
        template_buttons = []
    for row in ([] if isinstance(template_buttons,dict) else template_buttons):
        for button in row:
            if "url" in button: button_lines.append(f"{button.get('text','')} | URL | {button['url']}")
            elif "callback_data" in button: button_lines.append(f"{button.get('text','')} | CALLBACK | {str(button['callback_data']).removeprefix('act:')}")
    buttons_text = "\n".join(button_lines)
    if template_buttons:
        buttons_text=json.dumps({"mode":"inline","rows":[[{"text":b.get("text",""),"kind":"URL" if "url" in b else "CALLBACK","target":b.get("url",b.get("callback_data",""))} for b in row] for row in template_buttons]},ensure_ascii=False)
        buttons_text=restore_prompt_editor(buttons_text)
    selected_modes = template_config.get("content_modes", ["text"])
    sender_mode = template_config.get("sender_mode", "hide")
    send_gap_value = max(platform_send_gap_seconds(), float(template_config.get("send_gap_seconds") or platform_send_gap_seconds()))
    saved_media_assets = template_config.get("media_assets", {})
    selected_assets = {str(key): [str(item.get("id")) for item in value if isinstance(item, dict) and item.get("id") is not None]
                       for key, value in saved_media_assets.items() if isinstance(value, list)}
    content = """
    <div class="page-intro"><div><span class="eyebrow">Campaign / 群发中心</span><h1>创建群发任务</h1><p>选择机器人和目标群组，再勾选本次要发送的文字、图片或视频。</p></div><span class="soft-pill">Telegram 原生媒体库</span></div>
    <div class="card"><div class="section-head"><div><h2>从模板开始</h2><p>可以载入之前保存的群发配置，再修改本次发送内容。</p></div></div><select aria-label="选择消息模板" onchange="if(this.value) location.href='/broadcast?template_id='+this.value"><option value="">选择一个已保存的消息模板</option>{% for item in templates %}<option value="{{item.id}}">{{item.title}}（{{item.created_at}}）</option>{% endfor %}</select><p class="muted">模板只保存消息内容、媒体 file_id 和群组选择，不包含 Bot Token。</p></div>
    <form class="broadcast-form" method="post" id="broadcast-form"><input type="hidden" name="semantics" value="per_target"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}">
      <section class="card step-card"><div class="step-heading"><span class="step-number">01</span><div><h2>选择发送机器人</h2><p>选择负责发送消息的 Telegram Bot，可同时选择多个。</p></div><div class="step-tools"><button type="button" class="secondary" id="bots-all">全选</button><button type="button" class="secondary" id="bots-none">清空</button></div></div>
      {% if bots %}<div class="selection-grid">{% for b in bots %}<label class="selection-card"><input class="botcheck" type="checkbox" name="bot_ids" value="{{b.id}}" {% if not template_config or b.id|string in template_config.get('bot_ids',[]) %}checked{% endif %}><span class="selection-copy"><strong>{{b.first_name or 'Telegram Bot'}}</strong><small>@{{b.username}}</small></span></label>{% endfor %}</div>{% else %}<div class="helper-box">你还没有可用机器人。请先返回控制台添加机器人。</div><a class="btn secondary" href="/">前往添加机器人</a>{% endif %}</section>
      <section class="card step-card"><div class="step-heading"><span class="step-number">02</span><div><h2>选择目标群组</h2><p>只会向所选机器人已发现且状态正常的群组发送。</p></div><div class="step-tools"><button type="button" class="secondary" id="chats-all">全选可见群组</button><button type="button" class="secondary" id="chats-none">清空</button></div></div>
      {% if chats %}<div class="selection-grid" id="chat-grid">{% for g in chats %}<label class="selection-card chat-option" data-bot-id="{{g.bot_id}}"><input class="chatcheck" type="checkbox" name="chat_keys" value="{{g.bot_id}}:{{g.chat_id}}" {% if not template_config or (g.bot_id|string ~ ':' ~ g.chat_id|string) in template_config.get('chat_targets',[]) %}checked{% endif %}><span class="selection-copy"><strong>{{g.title}}</strong><small>@{{g.bot_username}} · {{g.chat_id}}</small></span></label>{% endfor %}</div>{% else %}<div class="helper-box">还没有发现群组。请先将机器人拉入目标群组，并确保它有发送权限。</div>{% endif %}<p class="muted" id="target-summary">已选择 0 个群组</p></section>
      <section class="card step-card"><div class="step-heading"><span class="step-number">03</span><div><h2>选择发送内容</h2><p>勾选哪种内容就发送哪种内容；可以只发一种，也可以组合发送。</p></div></div>
      <div class="content-choices"><label class="content-choice"><span class="choice-icon">T</span><span><strong>文字消息</strong><small>发送文字正文</small></span><input class="modecheck" type="checkbox" name="content_modes" value="text" {% if 'text' in selected_modes %}checked{% endif %}></label><label class="content-choice"><span class="choice-icon">▧</span><span><strong>图片</strong><small>从 Telegram 媒体库选择</small></span><input class="modecheck" type="checkbox" name="content_modes" value="photo" {% if 'photo' in selected_modes %}checked{% endif %}></label><label class="content-choice"><span class="choice-icon">▶</span><span><strong>视频</strong><small>从 Telegram 媒体库选择</small></span><input class="modecheck" type="checkbox" name="content_modes" value="video" {% if 'video' in selected_modes %}checked{% endif %}></label></div>
      <div class="field-block" id="text-content-block"><label for="broadcast-body">文字内容</label><textarea id="broadcast-body" name="body" placeholder="输入本次要发送的文字内容……">{{template_config.get('body','')}}</textarea><p class="muted">只有勾选“文字消息”时才会发送正文。</p></div>
      <div id="media-content-block">{% for b in bots %}<div class="media-library bot-media-library" data-bot-id="{{b.id}}"><h3>▧ @{{b.username}} 的 Telegram 媒体库</h3><p class="muted">勾选本机器人要发送的图片或视频，可多选。直接复制或转发 Telegram 原消息，保留原说明文字和按钮；选中相册任意一项会自动包含整组内容。</p>{% if media_assets_by_bot[b.id] %}<div class="media-list">{% for a in media_assets_by_bot[b.id] %}<label class="media-option" data-media-type="{{a.media_type}}"><input type="checkbox" name="media_assets_{{b.id}}" value="{{a.id}}" {% if a.id|string in selected_assets.get(b.id|string,[]) %}checked{% endif %}><span><strong>{{'图片' if a.media_type=='photo' else '视频'}}</strong><br>{{a.source_chat_title or 'Telegram'}} · {{(a.caption or '无说明')[:48]}}<br><small class="muted">{{a.created_at}}</small></span></label>{% endfor %}</div>{% else %}<div class="helper-box">暂无媒体素材。将机器人加入素材群并允许它接收消息，或把历史图片/视频转发给机器人私聊，收到后会自动加入媒体库。</div>{% endif %}</div>{% endfor %}</div>
      <div class="advanced-box"><details><summary>高级选项：文字轮换</summary><label for="rotation-messages">轮换消息（仅纯文字任务；每条消息之间单独一行“---轮换消息---”）</label><textarea id="rotation-messages" name="rotation_messages" placeholder="第一条轮换消息&#10;---轮换消息---&#10;第二条轮换消息">{{rotation_text}}</textarea><p class="muted">每个目标群组都会依次收到 A→B→C 全部消息；当前群组完成后再处理下一个群组。仅支持纯文字轮换。</p></details></div></section>
      <section class="card step-card"><div class="step-heading"><span class="step-number">04</span><div><h2>发送计划与附加功能</h2><p>可以立即发送，也可以预约时间、设置循环或新群自动发送。</p></div></div>
      <div class="field-grid"><div><label for="send-gap-seconds">群组发送间隔（秒，最低 {{platform_gap|int}} 秒）</label><input id="send-gap-seconds" name="send_gap_seconds" type="number" min="10" data-platform-min="{{platform_gap|int}}" max="3600" step="1" value="{{send_gap_value|int}}" required><small class="muted">可填写 {{platform_gap|int}} 秒或更长间隔，低于平台最低值将被拦截。</small></div><div><label>素材发送者名称</label><select name="sender_mode"><option value="hide" {% if sender_mode=='hide' %}selected{% endif %}>隐藏来源（复制素材）</option><option value="show" {% if sender_mode=='show' %}selected{% endif %}>显示来源（转发素材）</option></select><small class="muted">图片、视频优先复制或转发 Telegram 原消息，保留原文字说明和原按钮。</small></div><div><label for="scheduled_at">定时执行时间（留空则立即执行）</label><input id="scheduled_at" type="datetime-local" name="scheduled_at"><input type="hidden" id="tz_offset_minutes" name="tz_offset_minutes" value="0"></div><div><label><input type="checkbox" name="repeat_enabled" value="on"> 启用循环群发</label><small class="muted">每轮所有群组完成后，立即开始下一轮；不设置停止条件则永久执行。</small><label>定时停止</label><select name="repeat_duration_unit"><option value="none">不设置（永久执行）</option><option value="minutes">分钟</option><option value="hours">小时</option><option value="days">天</option></select><input type="number" name="repeat_duration_value" min="1" max="36500" placeholder="停止时长"><label>发送多少轮后停止（包含首次）</label><input type="number" name="repeat_max_runs" min="1" max="10000" placeholder="留空表示不限制"></div><div><label>自定义按钮（每行一个）</label><textarea name="buttons" placeholder="查看详情 | URL | https://example.com&#10;联系客服 | CALLBACK | contact">{{buttons_text}}</textarea></div></div>
      <div class="item"><label><input type="checkbox" name="auto_join_enabled" {% if template_config.get('auto_join_enabled', false) %}checked{% endif %}> 机器人以后被拉入新群时，自动发送本任务已选内容</label><p class="muted">仅群组/超级群组；机器人加入后延迟入队。新群必须允许机器人发送消息。结果未知时不会自动重复发送。</p></div><div class="helper-box">平台强制广告由管理员统一配置，并会按平台规则附加到每条群发消息。创建任务前请再次核对机器人、群组和内容类型。</div></section>
      <div class="submit-bar"><p id="broadcast-summary">请至少选择一个机器人、一个群组和一种发送内容。</p><button type="submit">确认并创建发送任务　→</button></div>
    </form>
    <script>(function(){const form=document.getElementById('broadcast-form');if(!form)return;const bots=Array.from(form.querySelectorAll('.botcheck'));const chats=Array.from(form.querySelectorAll('.chatcheck'));const modes=Array.from(form.querySelectorAll('.modecheck'));const bodyBlock=document.getElementById('text-content-block');const mediaBlock=document.getElementById('media-content-block');const targetSummary=document.getElementById('target-summary');const summary=document.getElementById('broadcast-summary');const checked=items=>items.filter(x=>x.checked);function refresh(){const selectedBots=checked(bots).map(x=>x.value);form.querySelectorAll('.chat-option').forEach(card=>{const visible=selectedBots.includes(card.dataset.botId);card.hidden=!visible;if(!visible){const input=card.querySelector('input');if(input)input.checked=false;}});form.querySelectorAll('.bot-media-library').forEach(card=>{card.hidden=!selectedBots.includes(card.dataset.botId);});const visibleChats=chats.filter(x=>!x.closest('.chat-option').hidden);const selectedChats=checked(visibleChats).length;const selectedModes=checked(modes).map(x=>x.value);bodyBlock.hidden=!selectedModes.includes('text');mediaBlock.hidden=!(selectedModes.includes('photo')||selectedModes.includes('video'));form.querySelectorAll('.media-option').forEach(card=>{card.hidden=!selectedModes.includes(card.dataset.mediaType);});const labels=selectedModes.map(x=>({text:'文字',photo:'图片',video:'视频'}[x]));targetSummary.textContent='已选择 '+selectedChats+' 个群组';summary.textContent='已选 '+selectedBots.length+' 个机器人 · '+selectedChats+' 个群组 · '+(labels.join('、')||'未选择发送内容');}document.getElementById('bots-all')?.addEventListener('click',()=>{bots.forEach(x=>x.checked=true);refresh();});document.getElementById('bots-none')?.addEventListener('click',()=>{bots.forEach(x=>x.checked=false);refresh();});document.getElementById('chats-all')?.addEventListener('click',()=>{chats.forEach(x=>{if(!x.closest('.chat-option').hidden)x.checked=true;});refresh();});document.getElementById('chats-none')?.addEventListener('click',()=>{chats.forEach(x=>x.checked=false);refresh();});form.addEventListener('change',refresh);refresh();const scheduleInput=document.getElementById('scheduled_at');const offsetInput=document.getElementById('tz_offset_minutes');scheduleInput.addEventListener('change',()=>{if(scheduleInput.value)offsetInput.value=new Date(scheduleInput.value).getTimezoneOffset();});form.addEventListener('submit',()=>{if(scheduleInput.value)offsetInput.value=new Date(scheduleInput.value).getTimezoneOffset();});})();</script>
    """

    return page(content,bots=bots,chats=chats,templates=templates,template_config=template_config,
                rotation_text=rotation_text,buttons_text=buttons_text,media_assets_by_bot=media_assets_by_bot,
                selected_modes=selected_modes,selected_assets=selected_assets,
                send_gap_value=send_gap_value, sender_mode=sender_mode)



@app.get("/bots/<int:bot_id>/profile")
@login_required
def export_bot_profile(bot_id):
    where, params = owner_clause("owner_user_id")
    with db() as c:
        bot=c.execute(f"SELECT telegram_id,username,first_name FROM bots WHERE id=? AND {where}",(bot_id,*params)).fetchone()
        if not bot: abort(404)
        chats=c.execute("SELECT chat_id,title,chat_type FROM chats WHERE bot_id=? ORDER BY title",(bot_id,)).fetchall()
    if not bot: abort(404)
    return jsonify({
        "schema":"tgadbot.bot-profile.v1",
        "note":"此文件不包含 Bot Token，不能复制 Telegram Bot 身份；新 Bot 必须由 BotFather 单独创建并重新加入目标群组。",
        "bot_public_info":dict(bot),
        "known_chats":[dict(x) for x in chats],
        "platform_settings":{"forced_ad_mode":forced_ad_mode()}
    })


@app.post("/series/<int:series_id>/<action>")
@login_required
def recurring_series_action(series_id, action):
    actions={"pause":pause_series,"resume":resume_series,"cancel":cancel_series}
    if action not in actions:
        abort(404)
    where, params = owner_clause("owner_user_id")
    with db() as c:
        owned = c.execute(f"SELECT id FROM recurring_series WHERE id=? AND {where}",(series_id,*params)).fetchone()
    if not owned: abort(404)
    ok,message=actions[action](series_id)
    flash(message)
    return redirect(url_for("history"))

@app.route("/history")
@login_required
def history():
    where, params = owner_clause("t.owner_user_id")
    where += " AND (t.status IN ('running','scheduled','paused','unknown') OR NOT EXISTS (SELECT 1 FROM log_visibility v WHERE v.owner_user_id=t.owner_user_id AND v.hidden_before>=COALESCE((SELECT MAX(activity.updated_at) FROM delivery_jobs activity WHERE activity.task_id=t.id),t.created_at)))"
    with db() as c:
        tasks=c.execute(f"SELECT t.*, (SELECT COUNT(*) FROM delivery_jobs d WHERE d.task_id=t.id) AS total_jobs, (SELECT COALESCE(SUM(CASE WHEN t.semantics='per_target' THEN d.success_count WHEN d.status='sent' THEN 1 ELSE 0 END),0) FROM delivery_jobs d WHERE d.task_id=t.id) AS sent_jobs, (SELECT COUNT(*) FROM delivery_jobs d WHERE d.task_id=t.id AND d.status='failed') AS failed_jobs, (SELECT COUNT(*) FROM delivery_jobs d WHERE d.task_id=t.id AND d.status='unknown') AS unknown_jobs FROM tasks t WHERE {where} ORDER BY t.id DESC LIMIT 200",params).fetchall()
        totals=c.execute(f"SELECT COUNT(*) AS total, SUM(CASE WHEN t.semantics='per_target' THEN d.success_count WHEN d.status='sent' THEN 1 ELSE 0 END) AS sent, SUM(CASE WHEN d.status='failed' THEN 1 ELSE 0 END) AS failed, SUM(CASE WHEN d.status='unknown' THEN 1 ELSE 0 END) AS unknown FROM delivery_jobs d JOIN tasks t ON t.id=d.task_id WHERE {where}",params).fetchone()
    content="""<form method="post" action="/history/clear"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button>清理我的发送日志</button><p>默认12小时自动隐藏已结束任务的日志；发送任务与原始记录保留。</p></form><div class="page-intro"><div><span class="eyebrow">Delivery / 发送记录</span><h1>群发历史</h1><p>查看每次任务的投递结果，追踪成功、失败和结果未知的群组。</p></div><a class="btn" href="/broadcast">＋ 新建群发</a></div>
    <div class="stats-grid"><div class="stat-card"><div class="stat-top">目标群组数<span class="stat-icon">▤</span></div><div class="stat-value">{{totals.total or 0}}</div><div class="stat-note">按任务统计的目标群组</div></div><div class="stat-card"><div class="stat-top">成功次数<span class="stat-icon">✓</span></div><div class="stat-value">{{totals.sent or 0}}</div><div class="stat-note">Telegram 已确认的成功次数</div></div><div class="stat-card"><div class="stat-top">失败目标<span class="stat-icon">!</span></div><div class="stat-value">{{totals.failed or 0}}</div><div class="stat-note">明确失败的投递</div></div><div class="stat-card"><div class="stat-top">结果未知<span class="stat-icon">?</span></div><div class="stat-value">{{totals.unknown or 0}}</div><div class="stat-note">需要人工核对，不会盲目重发</div></div></div>
    <div class="card"><div class="section-head"><div><h2>最近群发任务</h2><p>最多显示最近 200 个任务。</p></div><span class="status-pill">{{tasks|length}} 条记录</span></div><div class="table-scroll"><table><thead><tr><th>任务</th><th>状态</th><th>目标群组</th><th>成功次数</th><th>失败</th><th>未知</th><th>详情</th></tr></thead><tbody data-delivery-results>{% for t in tasks %}<tr><td><strong>#{{t.id}}</strong><br><small class="muted">{{t.created_at}}</small></td><td><span class="status-pill {% if t.status=='completed' %}success{% elif t.status in ['failed','cancelled'] %}error{% elif t.status in ['paused','unknown'] %}warning{% endif %}">{{t.status|status_zh}}</span></td><td>{{t.total_jobs}}</td><td>{{t.sent_jobs}}</td><td>{{t.failed_jobs}}</td><td>{{t.unknown_jobs}}</td><td><a href="/tasks/{{t.id}}">查看详情 →</a></td></tr>{% else %}<tr><td colspan="7" class="muted">暂无群发记录。</td></tr>{% endfor %}</tbody></table></div></div>"""
    return page(content,tasks=tasks,totals=totals)

@app.route("/tasks/<int:task_id>")
@login_required
def task_detail(task_id):
    where, params = owner_clause("owner_user_id")
    with db() as c:
        task=c.execute(f"SELECT * FROM tasks WHERE id=? AND {where}",(task_id,*params)).fetchone()
        if not task: abort(404)
        jobs=c.execute("SELECT * FROM delivery_jobs WHERE task_id=? ORDER BY id",(task_id,)).fetchall()
        last_activity=max((job["updated_at"] or task["created_at"] for job in jobs),default=task["created_at"])
        if task["status"] not in ("running","scheduled","paused","unknown") and c.execute("SELECT 1 FROM log_visibility WHERE owner_user_id=? AND hidden_before>=?",(task["owner_user_id"],last_activity)).fetchone():
            jobs=[]
        series=c.execute("SELECT * FROM recurring_series WHERE id=?",(task["series_id"],)).fetchone() if task and task["series_id"] else None
        join_jobs = c.execute(
            "SELECT chat_title,status,last_error FROM task_join_auto_sends WHERE task_id=? ORDER BY id DESC LIMIT 200",
            (task_id,),
        ).fetchall()
    if not task: abort(404)
    content="""<div class="page-intro"><div><span class="eyebrow">Task detail / 任务详情</span><h1>群发任务 #{{task.id}}</h1><p>查看本次任务的发送状态、群组结果和可执行操作。</p></div><a class="btn secondary" href="/history">← 返回群发历史</a></div>
    <div class="stats-grid"><div class="stat-card"><div class="stat-top">目标群组<span class="stat-icon">♧</span></div><div class="stat-value">{{jobs|length}}</div><div class="stat-note">本次任务投递目标</div></div><div class="stat-card"><div class="stat-top">成功次数<span class="stat-icon">✓</span></div><div class="stat-value">{{jobs|sum(attribute='success_count') if task.semantics=='per_target' else jobs|selectattr('status','equalto','sent')|list|length}}</div><div class="stat-note">已确认成功</div></div><div class="stat-card"><div class="stat-top">失败目标<span class="stat-icon">!</span></div><div class="stat-value">{{jobs|selectattr('status','equalto','failed')|list|length}}</div><div class="stat-note">明确失败的目标</div></div><div class="stat-card"><div class="stat-top">结果未知<span class="stat-icon">?</span></div><div class="stat-value">{{jobs|selectattr('status','equalto','unknown')|list|length}}</div><div class="stat-note">需要人工核对</div></div></div>
    <div class="card"><div class="section-head"><div><h2>任务概况</h2><p>创建时间：{{task.created_at}}</p></div><span class="status-pill {% if task.status=='completed' %}success{% elif task.status in ['failed','cancelled'] %}error{% elif task.status in ['paused','unknown'] %}warning{% endif %}">{{task.status|status_zh}}</span></div><div class="helper-box" data-live-summary>{{task.result or '任务正在等待处理。'}}<br>群组发送间隔：{{[task.send_gap_seconds or platform_gap, platform_gap]|max|round(1)}} 秒（平台最低 {{platform_gap|int}} 秒）</div>
    {% if series %}<hr><h2>循环发送系列 #{{series.id}}</h2><p>已完成 {{series.runs_created}} 轮；停止轮数：{{series.max_runs if series.max_runs else '不限'}}；定时停止：{{series.ends_at or '未设置'}}；当前状态：{{series.status|status_zh}}；下次计划：<span data-countdown="{{series.next_run_at}}" data-state="{{series.status}}"></span></p><div class="row">{% if series.status=='active' %}<form method="post" action="/series/{{series.id}}/pause"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button class="secondary">暂停整个循环</button></form>{% endif %}{% if series.status=='paused' %}<form method="post" action="/series/{{series.id}}/resume"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button>恢复整个循环</button></form>{% endif %}{% if series.status in ['active','paused','paused_unknown'] %}<form method="post" action="/series/{{series.id}}/cancel"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button class="danger">取消整个循环</button></form>{% endif %}</div>{% endif %}</div>
    <div class="card"><div class="section-head"><div><h2>群组投递明细</h2><p>逐个查看 Telegram 群组的发送状态和错误原因。</p></div><span class="status-pill">{{jobs|length}} 个目标</span></div>{% if task.status in ['running','scheduled','paused'] %}<p><a class="btn secondary" href="/tasks/{{task.id}}/edit">编辑任务内容与发送设置</a></p>{% endif %}<div class="table-scroll"><table><thead><tr><th>目标群组</th><th>状态</th><th>尝试次数</th><th>错误详情</th></tr></thead><tbody data-delivery-results>{% for j in jobs %}<tr><td><strong>{{j.chat_title}}</strong></td><td><span class="status-pill {% if j.status=='sent' %}success{% elif j.status=='failed' %}error{% elif j.status=='unknown' %}warning{% endif %}">{{j.status|status_zh}}</span></td><td>{{j.attempts}}</td><td>{{j.last_error or '—'}}</td></tr>{% else %}<tr><td colspan="4" class="muted">暂无投递记录。</td></tr>{% endfor %}</tbody></table></div><hr><div class="row"><form method="post" action="/tasks/{{task.id}}/clone"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button class="secondary">保存为可复用消息模板</button></form><form method="post" action="/tasks/{{task.id}}/retry_failed"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><button class="secondary">重试明确失败的投递</button></form></div><p class="muted">结果未知的投递不会自动重试，必须先人工核对群组中是否已收到消息。</p></div>"""
    content += """<section class="card"><h2>每群执行进度</h2><p>计数规则：{{"按群独立计数" if task.semantics=="per_target" else "按旧任务规则计数"}} · 配置版本 {{task.config_version}}</p><table data-live-progress><tr><th>目标</th><th>成功套数</th><th>下一素材位置</th><th>下次可发送时间（Unix 秒）</th></tr>{% for j in jobs %}<tr><td>{{j.chat_title}}</td><td>{{j.success_count}}</td><td>{{j.asset_cursor+1}}</td><td>{{j.next_attempt_at}}</td></tr>{% endfor %}</table><a href="/review?task_id={{task.id}}">处理待核对投递</a><form method="post" action="/tasks/{{task.id}}/archive"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><button class="secondary">归档已结束任务</button></form></section>"""
    content += """{% if task.auto_join_enabled or join_jobs %}<section class="card">
    <h2>新群自动发送</h2><p>{{'已开启' if task.auto_join_enabled else '已关闭'}}</p>
    <ul>{% for job in join_jobs %}<li>{{ job.chat_title }} · {{ job.status|status_zh }}
    {% if job.last_error %} · {{ job.last_error }}{% endif %}</li>
    {% else %}<li>暂无新群发送记录。</li>{% endfor %}</ul></section>{% endif %}"""
    return page(content,task=task,jobs=jobs,series=series,join_jobs=join_jobs)

@app.route("/tasks/<int:task_id>/edit", methods=["GET", "POST"])
@login_required
def edit_task(task_id):
    where, params = owner_clause("owner_user_id")
    with db() as c:
        task = c.execute(f"SELECT * FROM tasks WHERE id=? AND {where}", (task_id, *params)).fetchone()
        if not task:
            abort(404)
        task_bot_ids = [int(x) for x in json.loads(task["bot_ids"] or "[]")]
        bot_where, bot_params = owner_clause("bots.owner_user_id")
        bots = c.execute("SELECT id,username,first_name FROM bots WHERE status='active' AND owner_user_id=? ORDER BY id", (task['owner_user_id'],)).fetchall()
        available_chats = c.execute("SELECT g.*,b.username FROM chats g JOIN bots b ON b.id=g.bot_id WHERE b.owner_user_id=? AND b.status='active' AND g.status='active' ORDER BY b.id,g.title", (task['owner_user_id'],)).fetchall()
        jobs = c.execute("SELECT status FROM delivery_jobs WHERE task_id=?", (task_id,)).fetchall()
        series = c.execute("SELECT * FROM recurring_series WHERE id=?", (task["series_id"],)).fetchone() if task["series_id"] else None
        media_assets_by_bot = {str(bot["id"]): c.execute(
            "SELECT * FROM media_assets WHERE bot_id=? ORDER BY id DESC LIMIT 100", (bot["id"],)
        ).fetchall() for bot in bots}

    if task["status"] not in ("running", "scheduled", "paused"):
        flash("只有执行中、待执行或已暂停的任务可以编辑；已结束任务请使用克隆功能。")
        return redirect(url_for("task_detail", task_id=task_id))
    if any(row["status"] in ("sending", "unknown") for row in jobs):
        flash("当前任务存在正在发送或结果未知的群组，请先等待或核对发送结果后再编辑。")
        return redirect(url_for("task_detail", task_id=task_id))

    selected_modes = json.loads(task["content_modes"] or '["text"]')
    saved_media = json.loads(task["media_assets"] or "{}")
    selected_assets = {str(key): {str(item.get("id")) for item in value if isinstance(item, dict) and item.get("id") is not None}
                       for key, value in saved_media.items() if isinstance(value, list)}
    rotation_text = "\n---轮换消息---\n".join(json.loads(task["rotation_messages"] or "[]"))
    button_value = json.dumps({"mode": "inline", "rows": []}, ensure_ascii=False)
    task_buttons = json.loads(task["buttons"] or "[]")
    if task_buttons:
        source_rows = task_buttons.get("keyboard", []) if isinstance(task_buttons, dict) else task_buttons
        button_mode = "reply" if isinstance(task_buttons, dict) else "inline"
        button_value = json.dumps({"mode": button_mode, "rows": [[
            {"text": item.get("text", ""), "kind": "URL" if "url" in item else "CALLBACK",
             "target": item.get("url", str(item.get("callback_data", "")))}
            for item in row] for row in source_rows]}, ensure_ascii=False)
    button_value = restore_prompt_editor(button_value)
    repeat_enabled = (task["max_success"] != 1 or task["stop_after_seconds"] > 0) if task["semantics"] == "per_target" else bool(series and series["status"] in ("active", "paused"))
    repeat_duration_unit = "none"
    repeat_duration_value = ""
    repeat_max_runs_value = str(series["max_runs"]) if series and int(series["max_runs"] or 0) > 0 else ""
    if task["semantics"] == "per_target":
        repeat_max_runs_value = str(task["max_success"]) if task["max_success"] else ""
        if task["stop_after_seconds"]:
            repeat_duration_unit, repeat_duration_value = "minutes", str(task["stop_after_seconds"] // 60)
    if series and int(series["stop_after_seconds"] or 0) > 0:
        duration_seconds = int(series["stop_after_seconds"])
        if duration_seconds % 86400 == 0:
            repeat_duration_unit, repeat_duration_value = "days", str(duration_seconds // 86400)
        elif duration_seconds % 3600 == 0:
            repeat_duration_unit, repeat_duration_value = "hours", str(duration_seconds // 3600)
        else:
            repeat_duration_unit, repeat_duration_value = "minutes", str(max(1, duration_seconds // 60))
    if request.method == "POST":
        try:
            edited_keys = request.form.getlist('chat_keys') if 'targets_present' in request.form else json.loads(task['chat_targets'] or '[]')
            available = {f"{g['bot_id']}:{g['chat_id']}":g for g in available_chats}
            if 'targets_present' in request.form and (not edited_keys or any(k not in available for k in edited_keys)):
                raise ValueError('请选择本账号的有效目标群组。')
            target_bot_ids = {str(available[k]['bot_id']) for k in edited_keys if k in available} or {str(b) for b in task_bot_ids}
            scheduled_epoch = task['scheduled_at']
            if request.form.get('scheduled_at'):
                if task['started_at'] or any(r['status']=='sent' for r in jobs):
                    raise ValueError('任务已经开始，不能重新设置首次启动时间。')
                scheduled_epoch = parse_schedule_timestamp(request.form['scheduled_at'],request.form.get('tz_offset_minutes','0'))
            content_modes = [x for x in ("text", "photo", "video") if x in request.form.getlist("content_modes")]
            body = request.form.get("body", "").strip() if "text" in content_modes else ""
            rotation_messages = parse_rotation_messages(request.form.get("rotation_messages", "").strip())
            buttons = parse_buttons(request.form.get("buttons", ""))
            if isinstance(buttons, dict) and not isinstance(task_buttons, dict):
                raise ValueError("群发任务仅支持内联按钮；已有回复键盘的旧任务可保留原设置。")
            sender_mode = request.form.get("sender_mode", task["sender_mode"] or "hide")
            if sender_mode not in ("hide", "show"):
                raise ValueError("素材来源显示方式无效")
            send_gap_seconds = parse_send_gap_seconds(request.form.get("send_gap_seconds", max(float(task["send_gap_seconds"] or 0), platform_send_gap_seconds())))
            repeat_enabled = request.form.get("repeat_enabled") == "on"
            repeat_duration_seconds = 0
            repeat_max_runs = 0
            if repeat_enabled:
                duration_unit = request.form.get("repeat_duration_unit", "none")
                duration_value = int(request.form.get("repeat_duration_value", "0") or 0)
                repeat_max_runs = int(request.form.get("repeat_max_runs", "0") or 0)
                unit_seconds = {"none": 0, "minutes": 60, "hours": 3600, "days": 86400}
                if duration_unit not in unit_seconds:
                    raise ValueError("定时停止单位无效")
                if duration_unit == "none":
                    if duration_value:
                        raise ValueError("未选择定时单位时，请清空停止时长")
                elif not 1 <= duration_value <= 36500:
                    raise ValueError("定时停止时长必须为 1 至 36500")
                else:
                    repeat_duration_seconds = duration_value * unit_seconds[duration_unit]
                if not 0 <= repeat_max_runs <= 10000:
                    raise ValueError("循环轮数不能超过 10000；留空表示不限制")
            if not content_modes:
                raise ValueError("请至少选择一种发送内容。")
            if "text" in content_modes and not body and not rotation_messages:
                raise ValueError("已勾选文字发送，请填写文字内容。")
            if rotation_messages and content_modes != ["text"]:
                raise ValueError("消息轮换仅支持纯文字任务，请只勾选文字。")
            if rotation_messages and body:
                raise ValueError("使用轮换消息时，请将普通正文留空。")
            if len(rotation_messages) > 20 or any(len(item) > 4096 for item in rotation_messages):
                raise ValueError("每个任务最多 20 条轮换消息，单条不超过 4096 字符。")
            media_assets_by_bot = {}
            with db() as c:
                for bot in bots:
                    bid = str(bot["id"])
                    if bid not in target_bot_ids: continue
                    selected_ids = request.form.getlist(f"media_assets_{bid}")
                    selected = load_selected_media_assets(c, int(bid), selected_ids)
                    media_assets_by_bot[bid] = selected
                    for media_type in ("photo", "video"):
                        if media_type in content_modes and not any(item["type"] == media_type for item in selected):
                            raise ValueError(f"机器人 @{bot['username']} 尚未选择要发送的{'图片' if media_type == 'photo' else '视频'}。")
            if "photo" in content_modes or "video" in content_modes:
                if not any(media_assets_by_bot.values()):
                    raise ValueError("请从 Telegram 媒体库选择图片或视频。")
            ad_text = task["ad_text"] or ""
            text_candidates = rotation_messages if rotation_messages else ([body] if "text" in content_modes else [])
            if any(len(item + (("\n\n" + ad_text) if ad_text else "")) > 4096 for item in text_candidates):
                raise ValueError("文字消息与平台广告合计不能超过 4096 字符。")
            with db() as c:
                c.execute('BEGIN IMMEDIATE')
                fresh = c.execute('SELECT * FROM tasks WHERE id=?', (task_id,)).fetchone()
                expected = int(request.form.get('config_version', task['config_version']))
                if fresh['config_version'] != expected or fresh['status'] not in ('paused','scheduled','running'):
                    raise ValueError('任务已变化，请刷新后重新编辑。')
                if c.execute("SELECT 1 FROM delivery_jobs WHERE task_id=? AND status IN ('sending','unknown')", (task_id,)).fetchone():
                    raise ValueError('当前有在途或待核对消息，请稍后再保存。')
                c.execute('INSERT OR IGNORE INTO task_versions VALUES(?,?,?,?)', (task_id,fresh['config_version'],json.dumps(dict(fresh)),now()))
                c.execute('UPDATE tasks SET config_version=config_version+1 WHERE id=?', (task_id,))
                bind_prompt_actions(c, request.form.get('buttons', ''), target_bot_ids)
                # A partial logical delivery is immutable until its confirmed/unknown parts are reconciled.
                if c.execute("SELECT 1 FROM message_receipts r JOIN delivery_jobs j ON j.id=r.job_id WHERE j.task_id=? AND r.cycle=j.success_count AND r.status IN ('sent','sending','unknown')",(task_id,)).fetchone():
                    raise ValueError('有部分已发送的素材，请先完成或核对该次投递再改内容。')
                if 'targets_present' in request.form:
                    all_jobs = c.execute('SELECT * FROM delivery_jobs WHERE task_id=?',(task_id,)).fetchall()
                    existing_keys = {f"{j['bot_id']}:{j['chat_id']}":j for j in all_jobs}
                    for key,job in existing_keys.items():
                        if key not in edited_keys and job['status'] in ('pending','paused','failed'):
                            c.execute("UPDATE delivery_jobs SET status='cancelled',last_error='编辑移除目标，历史保留' WHERE id=?",(job['id'],))
                    for key in edited_keys:
                        if key not in existing_keys:
                            g=available[key]
                            c.execute("INSERT INTO delivery_jobs(task_id,bot_id,chat_id,chat_title,status,next_attempt_at,created_at,updated_at) VALUES(?,?,?,?,?,?,?,?)",(task_id,g['bot_id'],g['chat_id'],g['title'],'paused' if fresh['status']=='paused' else 'pending',max(int(time.time())+10,scheduled_epoch or 0),now(),now()))
                    c.execute('UPDATE tasks SET chat_targets=?,bot_ids=? WHERE id=?',(json.dumps(edited_keys),json.dumps(sorted(target_bot_ids)),task_id))
                if scheduled_epoch != fresh['scheduled_at']:
                    if fresh['started_at']:
                        raise ValueError('任务已经开始，请刷新页面。')
                    c.execute('UPDATE tasks SET scheduled_at=? WHERE id=?',(scheduled_epoch,task_id))
                c.execute("UPDATE delivery_jobs SET next_attempt_at=MAX(next_attempt_at,?,?) WHERE task_id=? AND status IN ('pending','paused')",(int(time.time())+math.ceil(send_gap_seconds),scheduled_epoch or 0,task_id))
                # Keep the next surviving asset when text slots are reordered or removed.
                old_rotation = json.loads(fresh['rotation_messages'] or '[]')
                if fresh['semantics']=='per_target' and old_rotation != rotation_messages:
                    for job in c.execute('SELECT id,asset_cursor FROM delivery_jobs WHERE task_id=?',(task_id,)).fetchall():
                        cursor=0
                        for delta in range(len(old_rotation)):
                            candidate=old_rotation[(job['asset_cursor']+delta)%len(old_rotation)]
                            if candidate in rotation_messages:
                                cursor=rotation_messages.index(candidate); break
                        c.execute('UPDATE delivery_jobs SET asset_cursor=? WHERE id=?',(cursor,job['id']))
                c.execute("""UPDATE tasks SET body=?,buttons=?,rotation_messages=?,content_modes=?,media_assets=?,send_gap_seconds=?,sender_mode=? WHERE id=?""",
                          (body, json.dumps(buttons, ensure_ascii=False), json.dumps(rotation_messages, ensure_ascii=False),
                           json.dumps(content_modes), json.dumps(media_assets_by_bot), send_gap_seconds, sender_mode, task_id))
                recurrence_config = {"bot_ids": sorted(target_bot_ids),
                    "chat_targets": edited_keys, "body": body, "buttons": buttons,
                    "ad_mode": task["ad_mode"], "ad_text": task["ad_text"],
                    "ad_button_text": task["ad_button_text"], "ad_url": task["ad_url"],
                    "media_path": task["media_path"], "media_type": task["media_type"],
                    "rotation_messages": rotation_messages, "content_modes": content_modes,
                    "media_assets": media_assets_by_bot, "auto_join_enabled": bool(task["auto_join_enabled"]),
                    "send_gap_seconds": send_gap_seconds, "sender_mode": sender_mode}
                if task['semantics'] == 'per_target':
                    duration_delta = repeat_duration_seconds - task['stop_after_seconds']
                    c.execute("UPDATE tasks SET max_success=?,stop_after_seconds=?,ends_at=CASE WHEN ?>0 AND started_at IS NOT NULL THEN started_at+pause_total+? ELSE NULL END WHERE id=?",
                              (repeat_max_runs if repeat_enabled else 1,repeat_duration_seconds,repeat_duration_seconds,repeat_duration_seconds,task_id))
                    c.execute("UPDATE delivery_jobs SET status='sent' WHERE task_id=? AND status IN ('pending','paused') AND success_count>=? AND ?>0",
                              (task_id,repeat_max_runs if repeat_enabled else 1,repeat_max_runs if repeat_enabled else 1))
                if task['semantics'] == 'legacy' and task["series_id"] and series:
                    if repeat_enabled and series["status"] in ("active", "paused"):
                        old_duration = int(series["stop_after_seconds"] or 0)
                        started_at = int(series["started_at"] or 0)
                        old_ends_at = int(series["ends_at"] or 0)
                        pause_adjustment = max(0, old_ends_at - (started_at + old_duration)) if started_at and old_ends_at and old_duration else 0
                        new_ends_at = started_at + repeat_duration_seconds + pause_adjustment if started_at and repeat_duration_seconds else None
                        c.execute("UPDATE recurring_series SET config_json=?,loop_mode='continuous',interval_seconds=0,max_runs=?,stop_after_seconds=?,ends_at=?,updated_at=? WHERE id=?",
                                  (json.dumps(recurrence_config, ensure_ascii=False), repeat_max_runs, repeat_duration_seconds,
                                   new_ends_at, now(), task["series_id"]))
                        if repeat_max_runs and int(series["runs_created"]) >= repeat_max_runs:
                            c.execute("UPDATE recurring_series SET status='completed',updated_at=? WHERE id=?", (now(), task["series_id"]))
                    elif not repeat_enabled:
                        c.execute("UPDATE recurring_series SET status='cancelled',updated_at=? WHERE id=?",
                                  (now(), task["series_id"]))
                elif repeat_enabled and task["semantics"] == "legacy":
                    run_at = int(task["scheduled_at"] or time.time())
                    c.execute("""INSERT INTO recurring_series
                        (config_json,interval_seconds,max_runs,runs_created,next_run_at,last_task_id,status,created_at,updated_at,owner_user_id,loop_mode,stop_after_seconds)
                        VALUES(?,0,?,1,?,?,'active',?,?,?,'continuous',?)""",
                        (json.dumps(recurrence_config, ensure_ascii=False), repeat_max_runs, run_at, task_id,
                         now(), now(), task["owner_user_id"], repeat_duration_seconds))
                    new_series_id = c.execute("SELECT last_insert_rowid() AS id").fetchone()["id"]
                    c.execute("UPDATE tasks SET series_id=? WHERE id=?", (new_series_id, task_id))
            flash("任务修改已保存；已发送群组不会撤回，修改只影响尚未发送的群组和后续循环。")
            return redirect(url_for("task_detail", task_id=task_id))
        except (ValueError, TypeError, json.JSONDecodeError) as exc:
            flash(str(exc) if isinstance(exc, ValueError) else "任务配置格式无效，请检查输入。")

    content = """<div class="page-intro"><div><span class="eyebrow">Task editor / 任务编辑</span><h1>编辑群发任务 #{{task.id}}</h1><p>修改只影响尚未发送的群组和后续循环；已发送消息不会撤回。</p></div><a class="btn secondary" href="/tasks/{{task.id}}">返回任务详情</a></div>
    <form method="post" class="broadcast-form"><input type="hidden" name="config_version" value="{{task.config_version}}"><input type="hidden" name="csrf_token" value="{{csrf_token()}}">
    <section class="card step-card"><h2>目标与启动时间</h2><input type="hidden" name="targets_present" value="1"><input type="hidden" name="tz_offset_minutes" value="0" data-timezone>{% for g in available_chats %}<label><input type="checkbox" name="chat_keys" value="{{g.bot_id}}:{{g.chat_id}}" {% if (g.bot_id|string ~ ':' ~ g.chat_id|string) in selected_chat_keys %}checked{% endif %}>{{g.title}} · @{{g.username}}</label>{% endfor %}<label>新的首次启动时间（留空保留；已开始任务不可修改）<input type="datetime-local" name="scheduled_at" {% if task.started_at %}disabled{% endif %}></label></section>
    <section class="card step-card"><h2>发送内容</h2><div class="content-choices"><label class="content-choice"><span><strong>文字消息</strong></span><input type="checkbox" name="content_modes" value="text" {% if 'text' in selected_modes %}checked{% endif %}></label><label class="content-choice"><span><strong>图片</strong></span><input type="checkbox" name="content_modes" value="photo" {% if 'photo' in selected_modes %}checked{% endif %}></label><label class="content-choice"><span><strong>视频</strong></span><input type="checkbox" name="content_modes" value="video" {% if 'video' in selected_modes %}checked{% endif %}></label></div>
    <label>文字正文</label><textarea name="body">{{task.body}}</textarea><div class="advanced-box"><details><summary>消息轮换 A→B→C</summary><label for="rotation-messages">每个群组按间隔依次收到 A、B、C，成功后推进</label><textarea id="rotation-messages" name="rotation_messages">{{rotation_text}}</textarea></details></div>
    {% for b in bots %}<div class="media-library"><h3>@{{b.username}} 的 Telegram 媒体库</h3><div class="media-list">{% for a in media_assets_by_bot[b.id|string] %}<label class="media-option"><input type="checkbox" name="media_assets_{{b.id}}" value="{{a.id}}" {% if a.id|string in selected_assets.get(b.id|string,[]) %}checked{% endif %}><span><strong>{{'图片' if a.media_type=='photo' else '视频'}}</strong><br>{{a.source_chat_title or 'Telegram'}} · {{(a.caption or '无说明')[:48]}}</span></label>{% endfor %}</div></div>{% endfor %}
    <label>自定义按钮（可视化编辑）</label><textarea name="buttons">{{button_value}}</textarea><label>素材发送者名称</label><select name="sender_mode"><option value="hide" {% if task.sender_mode!='show' %}selected{% endif %}>隐藏来源（复制素材）</option><option value="show" {% if task.sender_mode=='show' %}selected{% endif %}>显示来源（转发素材）</option></select><div class="advanced-box"><details open><summary>循环群发设置</summary><label><input type="checkbox" name="repeat_enabled" value="on" {% if repeat_enabled %}checked{% endif %}> 启用循环群发</label><small class="muted">新任务每群独立轮换素材；成功发送一套素材计一次，不设置停止条件则持续执行。</small><label>定时停止</label><select name="repeat_duration_unit"><option value="none" {% if repeat_duration_unit=='none' %}selected{% endif %}>不设置（永久执行）</option><option value="minutes" {% if repeat_duration_unit=='minutes' %}selected{% endif %}>分钟</option><option value="hours" {% if repeat_duration_unit=='hours' %}selected{% endif %}>小时</option><option value="days" {% if repeat_duration_unit=='days' %}selected{% endif %}>天</option></select><input type="number" name="repeat_duration_value" min="1" max="36500" value="{{repeat_duration_value}}" placeholder="停止时长"><label>每群成功次数上限（旧任务仍按轮数）</label><input type="number" name="repeat_max_runs" min="1" max="10000" value="{{repeat_max_runs_value}}" placeholder="留空表示不限制"></details></div><label>群组发送间隔（秒，最低 {{platform_gap|int}} 秒）</label><input type="number" name="send_gap_seconds" min="{{platform_gap|int}}" max="3600" step="1" value="{{[task.send_gap_seconds or platform_gap, platform_gap]|max|int}}" required><button type="submit">保存任务修改</button></section></form>"""
    return page(content, task=task, bots=bots, available_chats=available_chats,selected_chat_keys=json.loads(task["chat_targets"] or "[]"), media_assets_by_bot=media_assets_by_bot,
                selected_modes=selected_modes, selected_assets=selected_assets,
                rotation_text=rotation_text, button_value=button_value,
                repeat_enabled=repeat_enabled, repeat_duration_unit=repeat_duration_unit,
                repeat_duration_value=repeat_duration_value, repeat_max_runs_value=repeat_max_runs_value)


@app.post("/tasks/<int:task_id>/clone")
@login_required
def clone_task_template(task_id):
    with db() as c:
        where, params = owner_clause("owner_user_id")
        task=c.execute(f"SELECT * FROM tasks WHERE id=? AND {where}",(task_id,*params)).fetchone()
        if not task: abort(404)
        jobs=c.execute("SELECT bot_id,chat_id FROM delivery_jobs WHERE task_id=? ORDER BY sequence_no,id",(task_id,)).fetchall()
        config={"bot_ids":json.loads(task["bot_ids"]),
                "chat_targets":[f"{j['bot_id']}:{j['chat_id']}" for j in jobs],
                "body":task["body"],"buttons":json.loads(task["buttons"]),
                "rotation_messages":json.loads(task["rotation_messages"] or "[]"),
                "content_modes":json.loads(task["content_modes"] or '["text"]'),
                "media_assets":json.loads(task["media_assets"] or "{}"),
                "auto_join_enabled":bool(task["auto_join_enabled"]),
                "send_gap_seconds":float(task["send_gap_seconds"] or DEFAULT_TASK_SEND_GAP_SECONDS),
                "sender_mode":task["sender_mode"] or "hide"}
        c.execute("INSERT INTO task_templates(title,config_json,created_at,owner_user_id) VALUES(?,?,?,?)",
                  (f"任务 #{task_id} 模板",json.dumps(config,ensure_ascii=False),now(),current_owner_id()))
    flash("已保存消息模板；不会复制 Bot Token、账号身份或发送历史。")
    return redirect(url_for("broadcast",template_id="latest"))


def valid_web_url(url):
    try:
        parsed = urlparse(url)
        parsed.port
    except ValueError:
        return False
    return parsed.scheme in ("http", "https") and bool(parsed.hostname) and not any(
        char.isspace() or char == "\\" for char in url
    )


@app.route("/ads",methods=["GET","POST"])
@login_required
def ads():
    require_admin()
    if request.method=="POST":
        try:
            user_bot_limit = int(request.form.get("user_bot_limit", setting("user_bot_limit") or "0"))
            default_gap = int(request.form.get("default_send_gap_seconds", setting("default_send_gap_seconds") or str(int(DEFAULT_TASK_SEND_GAP_SECONDS))))
            if not 0 <= user_bot_limit <= 10000 or not MIN_TASK_SEND_GAP_SECONDS <= default_gap <= MAX_TASK_SEND_GAP_SECONDS:
                raise ValueError()
        except ValueError:
            flash("机器人数量请填 0 至 10000，默认群发间隔请填 10 至 3600 秒。")
            return redirect(url_for("ads"))
        sidebar_links = []
        names = request.form.getlist("sidebar_link_name")
        urls = request.form.getlist("sidebar_link_url")
        if len(names) != len(urls) or len(names) > 30:
            flash("侧边栏按钮配置不完整，最多添加 30 个。")
            return redirect(url_for("ads"))
        for name, url in zip(names, urls):
            name, url = name.strip(), url.strip()
            if not name and not url:
                continue
            if not name or len(name) > 60 or not valid_web_url(url):
                flash("请填写按钮名称和有效的 HTTP/HTTPS 链接。")
                return redirect(url_for("ads"))
            sidebar_links.append({"name": name, "url": url})
        new_ad_text=request.form.get("ad_text","").strip()
        new_button=request.form.get("ad_button_text","").strip()
        new_url=request.form.get("ad_url","").strip()
        mode=request.form.get("forced_ad_mode","BOTH")
        valid_mode = mode in ("TEXT_ONLY","BUTTON_ONLY","BOTH")
        valid_text = mode == "BUTTON_ONLY" or bool(new_ad_text)
        valid_button = mode == "TEXT_ONLY" or (bool(new_button) and valid_web_url(new_url))
        if not valid_mode or not valid_text or not valid_button:
            flash("请按广告模式填写对应的广告文字或按钮名称及有效 HTTP/HTTPS 链接。")
        else:
            previous_gap = platform_send_gap_seconds()
            settings = {
                "user_bot_limit": str(user_bot_limit),
                "default_send_gap_seconds": str(default_gap),
                "forced_ad_mode": mode,
                "ad_text": new_ad_text,
                "ad_button_text": new_button,
                "ad_url": new_url,
                "auto_join_enabled": "1" if request.form.get("auto_join_enabled") == "on" else "0",
                "auto_join_message": request.form.get("auto_join_message", "").strip(),
            }
            if "sidebar_links_present" in request.form:
                settings["sidebar_links"] = json.dumps(sidebar_links, ensure_ascii=False)
            with db() as c:
                c.executemany(
                    "INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                    settings.items(),
                )
                if default_gap > previous_gap:
                    c.execute(
                        """UPDATE delivery_jobs SET next_attempt_at=MAX(
                               next_attempt_at,
                               CAST(strftime('%s', updated_at) AS INTEGER)+?,
                               COALESCE((SELECT scheduled_at FROM tasks WHERE id=task_id),0))
                           WHERE status IN ('pending','paused') AND success_count>0
                           AND last_error IS NULL
                           AND task_id IN (
                               SELECT id FROM tasks
                               WHERE semantics='per_target'
                               AND status IN ('running','scheduled','paused','unknown')
                               AND COALESCE(send_gap_seconds, 0) < ?
                           )""",
                        (default_gap, default_gap),
                    )
                    c.execute(
                        """UPDATE delivery_jobs SET next_attempt_at=MAX(
                               ?, next_attempt_at+?,
                               COALESCE((SELECT scheduled_at FROM tasks WHERE id=task_id),0))
                           WHERE status IN ('pending','paused') AND last_error IS NULL
                           AND task_id IN (
                               SELECT id FROM tasks
                               WHERE semantics='legacy'
                               AND status IN ('running','scheduled','paused','unknown')
                               AND COALESCE(send_gap_seconds, 0) < ?
                           )
                           AND next_attempt_at>?""",
                        (int(time.time()), default_gap - previous_gap, default_gap, int(time.time())),
                    )
                    c.execute(
                        "UPDATE tasks SET send_gap_seconds=? "
                        "WHERE status IN ('running','scheduled','paused','unknown') "
                        "AND (send_gap_seconds IS NULL OR send_gap_seconds < ?)",
                        (default_gap, default_gap),
                    )

            flash("平台设置已保存。")
        return redirect(url_for("ads"))
    content="""<div class="page-intro"><div><span class="eyebrow">Platform / 平台配置</span><h1>平台设置</h1><p>统一配置平台广告规则和机器人入群自动发送行为。</p></div><span class="status-pill warning">管理员专属</span></div>
    <div class="card"><div class="section-head"><div><h2>强制平台广告</h2><p>广告由平台统一配置，普通用户不能关闭。</p></div><span class="status-pill success">当前模式：{{'文字' if ad_mode=='TEXT_ONLY' else '按钮' if ad_mode=='BUTTON_ONLY' else '文字 + 按钮'}}</span></div><form method="post"><input type="hidden" name="csrf_token" value="{{ csrf_token() }}"><h2>用户默认设置</h2><div class="field-grid"><div><label>每个用户最多添加的机器人数量</label><input type="number" name="user_bot_limit" min="0" max="10000" value="{{user_bot_limit}}"><small>0 表示不限数量。</small></div><div><label>平台最低群发间隔（秒）</label><input type="number" name="default_send_gap_seconds" min="10" max="3600" value="{{default_gap}}"></div></div><hr><label>广告展示方式</label><select name="forced_ad_mode"><option value="TEXT_ONLY" {% if ad_mode=='TEXT_ONLY' %}selected{% endif %}>只显示文字</option><option value="BUTTON_ONLY" {% if ad_mode=='BUTTON_ONLY' %}selected{% endif %}>只显示按钮</option><option value="BOTH" {% if ad_mode=='BOTH' %}selected{% endif %}>文字 + 按钮</option></select><label>广告文字（只显示按钮时可留空）</label><textarea name="ad_text">{{ad_text}}</textarea><div class="field-grid"><div><label>官方广告按钮名称</label><input name="ad_button_text" value="{{button_text}}"></div><div><label>官方广告跳转链接</label><input name="ad_url" value="{{ad_url}}" placeholder="https://example.com"></div></div><hr><h2>侧边栏自定义按钮</h2><input type="hidden" name="sidebar_links_present" value="1"><div data-sidebar-links>{% for link in sidebar_links %}<div class="field-grid" data-sidebar-link><input name="sidebar_link_name" value="{{link.name}}" maxlength="60" aria-label="按钮名称" placeholder="按钮名称"><input name="sidebar_link_url" value="{{link.url}}" type="url" aria-label="自定义链接" placeholder="https://"><button type="button" data-remove-sidebar-link class="secondary">删除</button></div>{% endfor %}</div><button type="button" data-add-sidebar-link class="secondary">添加自定义按钮</button><hr><h2>机器人入群自动发送</h2><label><input type="checkbox" name="auto_join_enabled" {% if auto_join_enabled=='1' %}checked{% endif %}> 新机器人加入群组后自动发送一次</label><label>入群自动发送内容</label><textarea name="auto_join_message">{{auto_join_message}}</textarea><p class="muted">仅群组/超级群组；检测到机器人从未加入变为成员/管理员后延迟 5 秒发送。同一机器人同一群组只创建一次记录。机器人必须具备发送权限；结果不确定时不会盲目重复发送。</p><button>保存平台设置</button></form></div>"""
    return page(content,user_bot_limit=setting("user_bot_limit") or "0",default_gap=setting("default_send_gap_seconds") or int(DEFAULT_TASK_SEND_GAP_SECONDS),ad_text=setting("ad_text"),button_text=setting("ad_button_text"),ad_url=setting("ad_url"),
                ad_mode=forced_ad_mode(),auto_join_enabled=setting("auto_join_enabled"),auto_join_message=setting("auto_join_message"))


@app.post("/history/clear")
@login_required
def clear_history():
    with db() as c:
        c.execute("INSERT INTO log_visibility(owner_user_id,hidden_before) VALUES(?,?) ON CONFLICT(owner_user_id) DO UPDATE SET hidden_before=excluded.hidden_before",(current_owner_id(),now()))
    flash("我的发送日志已清理，发送任务不受影响。")
    return redirect(url_for("history"))

@app.route("/admin/announcements",methods=["GET","POST"])
@login_required
def announcements_admin():
    require_admin()
    if request.method == "POST":
        try:
            action=request.form.get("action", "save")
            ident=int(request.form.get("id", "0") or 0)
            with db() as c:
                if action == "delete": c.execute("DELETE FROM announcements WHERE id=?",(ident,))
                elif action == "group":
                    link=request.form.get("official_group_url", "").strip()
                    u=urlparse(link)
                    if link and (u.scheme != "https" or u.hostname != "t.me"): raise ValueError("官方群须为 https://t.me/ 链接")
                    c.execute("INSERT INTO settings(key,value) VALUES('official_group_url',?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",(link,))
                else:
                    title=request.form.get("title", "").strip(); body=request.form.get("body", "").strip()
                    if not title or not body or len(title)>200 or len(body)>10000: raise ValueError("请填写公告标题和内容（最多200/10000字符）")
                    published=int(request.form.get("published_at", "") or time.time())
                    values=(title,body,int(request.form.get("enabled")=="on"),int(request.form.get("pinned")=="on"),published)
                    if ident: c.execute("UPDATE announcements SET title=?,body=?,enabled=?,pinned=?,published_at=? WHERE id=?",(*values,ident))
                    else: c.execute("INSERT INTO announcements(title,body,enabled,pinned,published_at) VALUES(?,?,?,?,?)",values)
            flash("已保存")
        except (ValueError,OverflowError): flash("输入无效，请检查标题、内容、发布时间和官方群链接。")
        return redirect(url_for("announcements_admin"))
    with db() as c: items=c.execute("SELECT * FROM announcements ORDER BY pinned DESC,published_at DESC").fetchall()
    return page("""<h1>公告与官方群</h1><form method="post"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><input type="hidden" name="action" value="group"><label>官方群链接</label><input name="official_group_url" value="{{group}}"><button>保存官方群</button></form>{% for n in items %}<form method="post" class="card"><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><input type="hidden" name="id" value="{{n.id}}"><input name="title" value="{{n.title}}" required><textarea name="body" required>{{n.body}}</textarea><label><input type="checkbox" name="enabled" {% if n.enabled %}checked{% endif %}>启用</label><label><input type="checkbox" name="pinned" {% if n.pinned %}checked{% endif %}>置顶</label><label>发布时间（Unix秒）</label><input type="number" name="published_at" value="{{n.published_at}}"><button>保存</button><button name="action" value="delete">删除</button></form>{% endfor %}<form method="post" class="card"><h2>新增公告</h2><input type="hidden" name="csrf_token" value="{{csrf_token()}}"><input name="title" placeholder="标题" required><textarea name="body" required></textarea><label><input type="checkbox" name="enabled" checked>启用</label><label><input type="checkbox" name="pinned">置顶</label><input type="number" name="published_at" placeholder="发布时间Unix秒，留空立即发布"><button>新增</button></form>""",items=items,group=setting("official_group_url"))

@app.get("/health")
def health():
    return {"ok":True,"service":"TG管家免费版","version":APP_VERSION}

import sys
import token_access
token_access.install(sys.modules[__name__])
material_library.install(sys.modules[__name__])
button_actions.install(sys.modules[__name__])
import operations
operations.install(sys.modules[__name__])

if __name__=="__main__":
    from runtime_lock import acquire
    acquire(DB_PATH)
    validate_config()
    init_db()
    start_pollers()
    start_delivery_worker()
    app.run(host=os.getenv("HOST","127.0.0.1"),port=int(os.getenv("PORT","8096")),debug=False,threaded=True)
