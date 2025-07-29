import asyncio
import io
import re
import math
import json
import logging
import shutil
import os
import sys
from logging.handlers import RotatingFileHandler
from datetime import datetime, timedelta
from typing import Callable, Dict, Any, Awaitable, List, Tuple

import pandas as pd
import plotly.graph_objects as go
import plotly.io as pio
from aiohttp import web
from dotenv import load_dotenv

from aiogram import Bot, Dispatcher, F, html, BaseMiddleware, types
from aiogram.types import Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton, BufferedInputFile, TelegramObject, User, ErrorEvent
from aiogram.filters import CommandStart, StateFilter, Command
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from aiogram.client.default import DefaultBotProperties
from aiogram.exceptions import TelegramBadRequest
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application

# --- КОНФИГУРАЦИЯ ---

# Загружаем переменные из файла .env (для локального запуска)
load_dotenv()

# ID администраторов (не меняются, вшиты в код)
ADMIN_IDS = [1893807986, 7559201607] # <-- ВАШИ ID АДМИНИСТРАТОРОВ

# Конфигурация из переменных окружения (или файла .env)
TOKEN = os.getenv("TELEGRAM_TOKEN")
WEBHOOK_URL = os.getenv("WEBHOOK_URL") # Нужен только для режима вебхука
LAUNCH_MODE = os.getenv("LAUNCH_MODE", "polling") # 'polling' (по умолчанию) или 'webhook'

# Проверка обязательных переменных
if not TOKEN:
    logging.critical("КРИТИЧЕСКАЯ ОШИБКА: Не найден TELEGRAM_TOKEN. Задайте его в .env файле или переменных окружения.")
    sys.exit(1)
if LAUNCH_MODE == "webhook" and not WEBHOOK_URL:
    logging.critical("КРИТИЧЕСКАЯ ОШИБКА: Для режима 'webhook' требуется WEBHOOK_URL.")
    sys.exit(1)

ADMIN_TELEGRAM_USERNAME = "weeloser"
FOUNDER_ID = ADMIN_IDS[0]
INITIAL_ADMIN_ID = ADMIN_IDS[1] if len(ADMIN_IDS) > 1 else None

# --- КОНСТАНТЫ ---
ITEMS_PER_PAGE = 5
LOGS_PER_PAGE = 10
DB_FILE = 'database.json'
STATS_FILE = 'stats.txt'
LOG_FILE = 'bot.log'
SPAM_LIMIT = 40
TIME_WINDOW = 60
BACKUP_INTERVAL_MINUTES = 15
CUSTOM_SIM_LIMIT = 15
CUSTOM_SIM_COOLDOWN_SECONDS = 60
PRIVATE_AUTODELETE_SECONDS = 0
GROUP_AUTODELETE_SECONDS = 600
GROUP_TYPES = ("group", "supergroup")

# --- ИНИЦИАЛИЗАЦИЯ ---
bot = Bot(token=TOKEN, default=DefaultBotProperties(parse_mode="HTML"))
dp = Dispatcher()
scheduler = AsyncIOScheduler(timezone="Europe/Moscow")
database = {}
user_timestamps = {}
broadcast_content = {}
STATS_CACHE = {}
message_owners: Dict[int, int] = {}
broadcast_queue = asyncio.Queue()

# --- СОСТОЯНИЯ FSM ---
class States(StatesGroup):
    get_broadcast_content = State()
    confirm_broadcast = State()
    get_group_broadcast_content = State()
    get_group_broadcast_pin_duration = State()
    confirm_group_broadcast = State()
    get_search_query = State()
    get_import_file = State()
    confirm_import_db = State()
    get_balance = State()
    get_risk = State()
    get_leverage = State()
    get_sim_type = State()
    get_limit_set_amount = State()
    update_stats_file = State()
    get_calc_ticker = State()
    get_calc_entry = State()
    get_calc_margin = State()
    get_calc_direction = State()
    get_calc_exits = State()
    confirm_add_trade_to_stats = State()

class RestoreStates(StatesGroup):
    awaiting_db = State()
    awaiting_stats = State()

# --- ФУНКЦИИ ВОССТАНОВЛЕНИЯ И БЭКАПА ---

async def request_files_from_admin(admin_list: List[int]):
    text = (
        "‼️ <b>ВНИМАНИЕ: Бот запущен без файлов данных!</b> ‼️\n\n"
        "Это штатная ситуация после перезапуска на хостинге.\n\n"
        "Для восстановления работы, пожалуйста, нажмите кнопку ниже и "
        "последовательно отправьте мне файлы `database.json` и `stats.txt`."
    )
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="▶️ Начать восстановление", callback_data="start_restore")]
    ])
    for admin_id in admin_list:
        try:
            await bot.send_message(admin_id, text, reply_markup=keyboard)
        except Exception as e:
            logging.error(f"Не удалось отправить запрос на восстановление админу {admin_id}: {e}")

@dp.callback_query(F.data == "start_restore")
async def handle_start_restore(call: CallbackQuery, state: FSMContext):
    if call.from_user.id not in ADMIN_IDS:
        return await call.answer("Эта функция только для администраторов.", show_alert=True)
    
    await state.set_state(RestoreStates.awaiting_db)
    await call.message.edit_text(
        "✅ <b>Процесс восстановления начат.</b>\n\n"
        "<b>Шаг 1/2:</b> Пожалуйста, отправьте файл `database.json`."
    )
    await call.answer()

@dp.message(StateFilter(RestoreStates.awaiting_db), F.document)
async def handle_db_restore(message: Message, state: FSMContext):
    if message.document.file_name != DB_FILE:
        return await message.reply(f"❌ Ошибка. Ожидается файл с именем `{DB_FILE}`. Вы прислали `{message.document.file_name}`.")
    
    await bot.download(message.document, destination=DB_FILE)
    await message.reply(
        f"✅ Файл `{DB_FILE}` успешно получен.\n\n"
        f"<b>Шаг 2/2:</b> Теперь, пожалуйста, отправьте файл `stats.txt`."
    )
    await state.set_state(RestoreStates.awaiting_stats)

@dp.message(StateFilter(RestoreStates.awaiting_stats), F.document)
async def handle_stats_restore(message: Message, state: FSMContext):
    if message.document.file_name != STATS_FILE:
        return await message.reply(f"❌ Ошибка. Ожидается файл с именем `{STATS_FILE}`. Вы прислали `{message.document.file_name}`.")

    await bot.download(message.document, destination=STATS_FILE)
    await message.reply(f"✅ Файл `{STATS_FILE}` получен. Начинаю инициализацию...")
    
    await state.clear()

    try:
        await initialize_bot_data()
        await message.answer("✅ <b>Бот успешно восстановлен и полностью готов к работе!</b>")
        logging.info("Бот успешно восстановлен из файлов, предоставленных администратором.")
    except Exception as e:
        logging.critical(f"Критическая ошибка во время инициализации после восстановления: {e}")
        await message.answer(f"❌ <b>Произошла критическая ошибка при инициализации:</b>\n\n<pre>{html.quote(str(e))}</pre>")

async def scheduled_files_backup():
    if not os.path.exists(DB_FILE) or not os.path.exists(STATS_FILE):
        logging.warning("Пропуск планового бэкапа: файлы данных отсутствуют.")
        return

    logging.info("Запуск задачи резервного копирования файлов...")
    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M')
    
    try:
        db_file = BufferedInputFile.from_file(DB_FILE, filename=f"backup_{DB_FILE}")
        stats_file = BufferedInputFile.from_file(STATS_FILE, filename=f"backup_{STATS_FILE}")
        
        for admin_id in ADMIN_IDS:
            try:
                await bot.send_document(admin_id, db_file, caption=f"Автоматический бэкап БД\n{timestamp}", disable_notification=True)
                await bot.send_document(admin_id, stats_file, caption=f"Автоматический бэкап статистики\n{timestamp}", disable_notification=True)
            except Exception as e:
                logging.error(f"Не удалось отправить бэкап админу {admin_id}: {e}")
            await asyncio.sleep(0.5)
        logging.info("Резервное копирование файлов успешно завершено.")
    except Exception as e:
        logging.error(f"Критическая ошибка в задаче резервного копирования файлов: {e}")

# --- ОСНОВНАЯ ЛОГИКА БОТА ---

async def initialize_stats_file():
    try:
        with open(STATS_FILE, 'r', encoding='utf-8') as f:
            if not f.read().strip():
                logging.warning(f"Файл {STATS_FILE} пуст. Пожалуйста, заполните его.")
    except FileNotFoundError:
        logging.warning(f"Файл {STATS_FILE} не найден. Создаю пустой файл-шаблон.")
        template = """--- Статистика: Илья Власов - Грабитель ММ ---
Чистое движение: 0%
Винрейт: 0%
Всего сделок: 0
Успешных: 0
Убыточных: 0
В безубыток: 0
В отработке: 0


Начало - 01.01.25
Последнее обновление - 01.01.25
Если нашли ошибку/опечатку = t.me/weeloser



--- Статистика: Илья Власов - Грабитель ММ ---

ПРИМЕР СДЕЛКИ (long)
Чистое движение: 5.00%
ENTRY: 100
Маржа: X1
Фиксации: 105 (100%)
Дата: 01.01.2025
"""
        with open(STATS_FILE, 'w', encoding='utf-8') as f:
            f.write(template)

async def create_stats_backup():
    backup_filename = f"stats_backup_{datetime.now().strftime('%Y-%m-%d_%H-%M-%S')}.txt"
    try:
        shutil.copy(STATS_FILE, backup_filename)
        logging.info(f"Создана резервная копия статистики: {backup_filename}")
        return True
    except Exception as e:
        logging.error(f"Не удалось создать резервную копию stats.txt: {e}")
        return False

async def load_database():
    global database
    try:
        with open(DB_FILE, 'r', encoding='utf-8') as f:
            database = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        database = {}
    if 'users' not in database: database['users'] = {}
    if 'admins' not in database: database['admins'] = ADMIN_IDS
    if 'action_log' not in database: database['action_log'] = []
    if 'group_chats' not in database: database['group_chats'] = []
    await save_database()

async def save_database():
    try:
        if 'group_chats' in database and isinstance(database['group_chats'], set):
            database['group_chats'] = list(database['group_chats'])
        with open(DB_FILE, 'w', encoding='utf-8') as f:
            json.dump(database, f, indent=4, ensure_ascii=False)
    except Exception as e:
        logging.error(f"Ошибка сохранения БД: {e}")

async def save_context_message(user_id: int, message_id: int):
    user_id_str = str(user_id)
    if user_id_str in database['users']:
        database['users'][user_id_str]['context_message_id'] = message_id
        await save_database()

async def delete_context_message(user_id: int, chat_id: int):
    user_id_str = str(user_id)
    user_data = database['users'].get(user_id_str, {})
    msg_id = user_data.get('context_message_id')
    if msg_id:
        try:
            await bot.delete_message(chat_id, msg_id)
        except TelegramBadRequest:
            pass
        if user_id_str in database['users']:
            database['users'][user_id_str]['context_message_id'] = None
            await save_database()

def get_user_sim_limit(user_id: int) -> int:
    user_id_str = str(user_id)
    user_data = database['users'].get(user_id_str, {})
    today = datetime.now().strftime("%Y-%m-%d")
    if 'limits' not in user_data or user_data.get('limits', {}).get('date') != today:
        user_data['limits'] = {'date': today, 'used_count': 0}
        database['users'][user_id_str] = user_data
    return user_data['limits']['used_count']

async def increment_user_sim_limit(user_id: int):
    user_id_str = str(user_id)
    get_user_sim_limit(user_id)
    database['users'][user_id_str]['limits']['used_count'] += 1
    await save_database()

async def set_user_sim_attempts(user_id: int, remaining_amount: int):
    user_id_str = str(user_id)
    get_user_sim_limit(user_id)
    new_used_count = CUSTOM_SIM_LIMIT - remaining_amount
    database['users'][user_id_str]['limits']['used_count'] = max(0, new_used_count)
    await save_database()
    return CUSTOM_SIM_LIMIT - database['users'][user_id_str]['limits']['used_count']

def _parse_stats_data_sync(content: str = None) -> Tuple[Dict, List]:
    lines = []
    if content is None:
        try:
            with open(STATS_FILE, 'r', encoding='utf-8') as f:
                lines = f.readlines()
        except FileNotFoundError:
            logging.error(f"Файл статистики '{STATS_FILE}' не найден!")
            return {}, []
    else:
        lines = content.splitlines(keepends=True)

    summary, trades = {}, []
    separator = '--- Статистика: Илья Власов - Грабитель ММ ---'
    
    try:
        sep_indices = [i for i, line in enumerate(lines) if separator in line]
        if len(sep_indices) < 2:
            logging.error("Неверный формат файла stats.txt: не найдены разделители.")
            return {}, []

        summary_lines = lines[sep_indices[0] + 1 : sep_indices[1]]
        summary_content = "".join(summary_lines)
        summary_regex = (
            r"Чистое движение:\s*(.*?)\s*\n"
            r"Винрейт:\s*(.*?)\s*\n"
            r"Всего сделок:\s*(.*?)\s*\n"
            r"Успешных:\s*(.*?)\s*\n"
            r"Убыточных:\s*(.*?)\s*\n"
            r"В безубыток:\s*(.*?)\s*\n"
            r"В отработке:\s*(.*?)\s*\n\s*"
            r"Начало\s*-\s*(.*?)\s*\n"
            r"Последнее обновление\s*-\s*(.*?)\s*\n"
        )
        summary_match = re.search(summary_regex, summary_content)
        if summary_match:
            keys = ["total_pnl", "winrate", "total_deals", "successful", "losing", "breakeven", "in_progress", "start_date", "last_update"]
            summary = dict(zip(keys, [g.strip() for g in summary_match.groups()]))

        trades_content = "".join(lines[sep_indices[1] + 1:])
        trade_blocks = re.split(r'\n\s*\n+(?=[A-Z0-9]+\s+\((?:long|short)\))', trades_content.strip())
        
        for i, block in enumerate(trade_blocks):
            if not block.strip(): continue
            
            trade = {'in_progress': False, 'original_index': i}
            block_lines = [line.strip() for line in block.strip().split('\n') if line.strip()]
            if not block_lines: continue

            title_match = re.match(r"(.+?)\s+\((long|short)\)", block_lines[0])
            if title_match:
                trade['ticker'], trade['type'] = title_match.groups()
            else:
                logging.warning(f"Пропуск блока сделки с неверным форматом заголовка: {block_lines[0]}")
                continue
            
            for line in block_lines[1:]:
                if ':' in line:
                    key, value = [x.strip() for x in line.split(':', 1)]
                    key_map = {'чистое движение': 'pnl', 'entry': 'entry', 'маржа': 'margin', 'фиксации': 'exits', 'дата': 'date'}
                    
                    if key.lower() == 'фиксации' and 'в отработке' in value.lower():
                        trade['in_progress'] = True
                    
                    trade[key_map.get(key.lower())] = value

            if trade['in_progress']:
                trade['pnl_value'] = 0.0
            elif 'pnl' in trade:
                try:
                    trade['pnl_value'] = float(trade['pnl'].replace('%', ''))
                except (ValueError, TypeError):
                    trade['pnl_value'] = 0.0

            if 'date' in trade:
                try:
                    trade['date_dt'] = datetime.strptime(trade['date'], "%d.%m.%Y")
                except ValueError:
                    try:
                        trade['date_dt'] = datetime.strptime(trade['date'], "%d.%m.%y")
                    except ValueError:
                        continue
            
            if 'ticker' in trade:
                trades.append(trade)
    except Exception as e:
        logging.error(f"Ошибка при парсинге stats.txt: {e}")
        return {}, []
        
    return summary, trades

async def parse_stats_data():
    return await asyncio.to_thread(_parse_stats_data_sync)

def _calculate_streaks_sync(trades: List[Dict]) -> Tuple[int, int, int]:
    if not trades: return 0, 0, 0
    
    streaks = {'win': 0, 'loss': 0, 'be': 0}
    max_streaks = {'win': 0, 'loss': 0, 'be': 0}
    
    completed_trades = [t for t in trades if not t.get('in_progress') and 'date_dt' in t]
    chrono_trades = sorted(completed_trades, key=lambda x: (x['date_dt'], -x.get('original_index', 0)))

    for trade in chrono_trades:
        pnl = trade.get('pnl_value', 0)
        if pnl > 0:
            streaks['win'] += 1
            streaks['loss'] = 0
            streaks['be'] = 0
        elif pnl < 0:
            streaks['loss'] += 1
            streaks['win'] = 0
            streaks['be'] = 0
        else:
            streaks['be'] += 1
            streaks['win'] = 0
            streaks['loss'] = 0
            
        max_streaks['win'] = max(max_streaks['win'], streaks['win'])
        max_streaks['loss'] = max(max_streaks['loss'], streaks['loss'])
        max_streaks['be'] = max(max_streaks['be'], streaks['be'])
        
    return max_streaks['win'], max_streaks['loss'], max_streaks['be']

async def _create_chart_versions(fig: go.Figure, html_title: str = "Интерактивный график") -> Tuple[io.BytesIO, io.BytesIO]:
    def _sync_worker():
        config = {'displaylogo': False, 'modeBarButtonsToRemove': ['lasso2d', 'select2d'], 'scrollZoom': True}
        html_fig_str = pio.to_html(fig, full_html=False, include_plotlyjs='cdn', config=config)
        full_html = f"""
        <!DOCTYPE html><html><head><meta charset="UTF-8"><title>{html.quote(html_title)}</title>
        <style>body {{ margin: 0; background-color: #111; }}</style></head><body>{html_fig_str}</body></html>
        """
        html_buf = io.BytesIO(full_html.encode('utf-8'))
        html_buf.seek(0)
        
        fig.update_layout(paper_bgcolor='rgba(0,0,0,0)', plot_bgcolor='rgba(0,0,0,0)')
        img_bytes = pio.to_image(fig, format='png', scale=2, width=800, height=450)
        png_buf = io.BytesIO(img_bytes)
        png_buf.seek(0)
        return html_buf, png_buf
    return await asyncio.to_thread(_sync_worker)

async def plot_summary_chart(summary: Dict) -> io.BytesIO | None:
    def _sync_worker():
        try:
            labels = ['Успешных', 'Убыточных', 'В безубыток']
            values = [int(summary.get('successful', 0)), int(summary.get('losing', 0)), int(summary.get('breakeven', 0))]
            colors = ['#4CAF50', '#F44336', '#9E9E9E']
            if sum(values) == 0: return None
        except (ValueError, TypeError):
            logging.error("Ошибка преобразования данных для кругового графика.")
            return None
            
        fig = go.Figure(data=[go.Pie(labels=labels, values=values, hole=.3, marker_colors=colors, textinfo='percent+label', pull=[0.05, 0, 0])])
        fig.update_layout(title_text='Соотношение сделок', template='plotly_dark', font=dict(color='white'), showlegend=False)
        
        fig.update_layout(paper_bgcolor='rgba(0,0,0,0)', plot_bgcolor='rgba(0,0,0,0)')
        img_bytes = pio.to_image(fig, format='png', scale=2, width=800, height=450)
        png_buf = io.BytesIO(img_bytes)
        png_buf.seek(0)
        return png_buf
    return await asyncio.to_thread(_sync_worker)

async def plot_pnl_chart(trades: List[Dict]) -> Tuple[io.BytesIO, io.BytesIO] | Tuple[None, None]:
    def _sync_worker():
        completed_trades = [t for t in trades if not t.get('in_progress') and 'date_dt' in t]
        if not completed_trades: return None, None
        
        chrono_trades = sorted(completed_trades, key=lambda x: (x['date_dt'], -x.get('original_index', 0)))
        
        df = pd.DataFrame(chrono_trades)
        if 'pnl_value' not in df.columns: return None, None
        df['cumulative_pnl'] = df['pnl_value'].cumsum()
        
        hover_texts = [f"<b>{row['ticker']}</b><br>PnL сделки: {row['pnl_value']:.2f}%" for index, row in df.iterrows()]

        fig = go.Figure()
        fig.add_trace(go.Scatter(
            x=df.index, y=df['cumulative_pnl'], mode='lines+markers', name='Кумулятивный PnL',
            text=hover_texts, hovertemplate="""%{text}<br><b>Итоговый PnL: %{y:.2f}%</b><br>Сделка №%{x}<extra></extra>"""
        ))
        fig.update_layout(title='Динамика общего PnL (%)', xaxis_title='Номер сделки', yaxis_title='Кумулятивный PnL (%)', template='plotly_dark', font=dict(color='white'))
        return fig

    fig = await asyncio.to_thread(_sync_worker)
    if fig is None: return None, None
    return await _create_chart_versions(fig, html_title="Интерактивный график PnL")

async def calculate_simulation(trades, sim_type, initial_balance, risk_percent, leverage) -> Dict:
    def _sync_worker():
        current_balance = initial_balance
        balance_history = [0.0]
        completed_trades = [t for t in trades if not t.get('in_progress') and 'date_dt' in t]
        
        chrono_trades = sorted(completed_trades, key=lambda x: (x['date_dt'], -x.get('original_index', 0)))

        for trade in chrono_trades:
            pnl_percent = trade.get('pnl_value', 0.0)
            trade_capital = current_balance * (risk_percent / 100.0) if sim_type == 'compound' else initial_balance * (risk_percent / 100.0)
            position_size = trade_capital * leverage
            profit_or_loss = position_size * (pnl_percent / 100.0)
            current_balance += profit_or_loss
            growth_percent = (current_balance / initial_balance - 1) * 100 if initial_balance > 0 else 0
            balance_history.append(growth_percent)
        return {'min_percent': min(balance_history), 'max_percent': max(balance_history), 'final_percent': balance_history[-1], 'final_balance': current_balance, 'history': balance_history}
    return await asyncio.to_thread(_sync_worker)

async def plot_simulation_chart(history: List[float]) -> Tuple[io.BytesIO, io.BytesIO] | Tuple[None, None]:
    def _sync_worker():
        if not history: return None
        fig = go.Figure()
        fig.add_trace(go.Scatter(
            x=list(range(len(history))), y=history, mode='lines+markers', name='Изменение депозита',
            line=dict(color='#FFD700', width=2), marker=dict(size=5),
            hovertemplate="Сделка №%{x}<br><b>Изменение депозита: %{y:.2f}%</b><extra></extra>"
        ))
        fig.update_layout(title_text='Симуляция изменения депозита', xaxis_title='Номер сделки', yaxis_title='Изменение депозита (%)', template='plotly_dark', font=dict(color='white'))
        return fig
    
    fig = await asyncio.to_thread(_sync_worker)
    if fig is None: return None, None
    return await _create_chart_versions(fig, html_title="Интерактивная симуляция")

async def update_stats_cache():
    logging.info("Обновление кэша статистики...")
    summary, trades = await parse_stats_data()
    if not summary and not trades:
        logging.error("Не удалось загрузить данные для кэша. Проверьте stats.txt")
        return

    STATS_CACHE["summary"] = summary
    STATS_CACHE["trades"] = trades
    
    win_streak, loss_streak, be_streak = await asyncio.to_thread(_calculate_streaks_sync, trades)
    STATS_CACHE["streaks"] = {"win": win_streak, "loss": loss_streak, "be": be_streak}
    
    pnl_html, pnl_png = await plot_pnl_chart(trades)
    STATS_CACHE["pnl_chart_html"], STATS_CACHE["pnl_chart_png"] = pnl_html, pnl_png
    STATS_CACHE["summary_chart_png"] = await plot_summary_chart(summary)

    sim_compound_results = await calculate_simulation(trades, 'compound', 1000.0, 3.0, 35.0)
    STATS_CACHE["sim_compound_results"] = sim_compound_results
    if sim_compound_results and sim_compound_results['history']:
        sim_compound_html, sim_compound_png = await plot_simulation_chart(sim_compound_results['history'])
        STATS_CACHE["sim_compound_chart_html"], STATS_CACHE["sim_compound_chart_png"] = sim_compound_html, sim_compound_png

    sim_simple_results = await calculate_simulation(trades, 'simple', 1000.0, 3.0, 35.0)
    STATS_CACHE["sim_simple_results"] = sim_simple_results
    if sim_simple_results and sim_simple_results['history']:
        sim_simple_html, sim_simple_png = await plot_simulation_chart(sim_simple_results['history'])
        STATS_CACHE["sim_simple_chart_html"], STATS_CACHE["sim_simple_chart_png"] = sim_simple_html, sim_simple_png

    logging.info("Кэш статистики успешно обновлен.")

class AuthMiddleware(BaseMiddleware):
    async def __call__(self, handler: Callable[[TelegramObject, Dict[str, Any]], Awaitable[Any]], event: TelegramObject, data: Dict[str, Any]) -> Any:
        if isinstance(event, (Message, CallbackQuery)) and event.chat.type == 'channel':
            return

        chat = data.get('event_chat')
        if chat and chat.type in GROUP_TYPES:
            if 'group_chats' not in database: database['group_chats'] = set()
            elif isinstance(database['group_chats'], list): database['group_chats'] = set(database['group_chats'])
            
            if chat.id not in database['group_chats']:
                database['group_chats'].add(chat.id)
                await save_database()

        user: User | None = data.get('event_from_user')
        if not user: return await handler(event, data)

        if isinstance(event, CallbackQuery):
            owner_id = message_owners.get(event.message.message_id)
            if owner_id and owner_id != user.id:
                await event.answer("Это меню не для вас.", show_alert=True)
                return

        if database.get('users', {}).get(str(user.id), {}).get('is_banned'):
            if isinstance(event, CallbackQuery): await event.answer("Вы заблокированы.", show_alert=True)
            return
        
        now = datetime.now().timestamp()
        if user.id not in user_timestamps: user_timestamps[user.id] = []
        user_timestamps[user.id] = [t for t in user_timestamps[user.id] if now - t < TIME_WINDOW]
        user_timestamps[user.id].append(now)
        if len(user_timestamps[user.id]) > SPAM_LIMIT and not is_admin(user.id):
            user_id_str = str(user.id)
            if not database.get('users', {}).get(user_id_str, {}).get('is_banned'):
                database['users'][user_id_str] = {'is_banned': True}
                await save_database()
                try:
                    sent_msg = await bot.send_message(user.id, f"Вы были автоматически заблокированы за спам.\nДля разблокировки обратитесь к @{ADMIN_TELEGRAM_USERNAME}")
                    asyncio.create_task(delete_message_after_delay(sent_msg, sent_msg.chat.type))
                except TelegramBadRequest: pass
                username = f"@{user.username}" if user.username else f"id:{user_id_str}"
                await log_system_action(f"‼️ Пользователь {html.quote(username)} (<code>{user_id_str}</code>) был автоматически забанен за спам.")
            return
        
        await update_user_data(user)
        return await handler(event, data)

def get_user_mention(user: User) -> str:
    return f'<a href="tg://user?id={user.id}">{html.quote(user.first_name)}</a>'

async def delete_message_after_delay(message: Message, chat_type: str):
    delay = GROUP_AUTODELETE_SECONDS if chat_type in GROUP_TYPES else PRIVATE_AUTODELETE_SECONDS
    if delay <= 0: return
    
    await asyncio.sleep(delay)
    try:
        await message.delete()
        if message.message_id in message_owners:
            del message_owners[message.message_id]
    except TelegramBadRequest: pass

async def unpin_message_after_delay(chat_id: int, message_id: int, delay: int):
    if delay <= 0: return
    await asyncio.sleep(delay)
    try:
        await bot.unpin_chat_message(chat_id, message_id)
    except TelegramBadRequest as e:
        logging.warning(f"Не удалось открепить сообщение {message_id} в чате {chat_id}: {e}")

async def update_user_data(user: User):
    user_id_str = str(user.id)
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    if user_id_str not in database['users']:
        database['users'][user_id_str] = {
            'username': user.username, 'first_name': user.first_name, 'last_name': user.last_name, 
            'first_start': now, 'last_activity': now, 'message_count': 1, 'is_banned': False, 
            'context_message_id': None, 'last_sim_time': None
        }
    else:
        user_db_entry = database['users'][user_id_str]
        user_db_entry['last_activity'] = now
        user_db_entry['message_count'] = user_db_entry.get('message_count', 0) + 1
        user_db_entry['username'] = user.username
        user_db_entry['first_name'] = user.first_name
        user_db_entry['last_name'] = user.last_name
    await save_database()

async def log_user_action(user: User, action_text: str):
    log_entry = {
        "user_id": user.id, "username": user.username or "N/A", "first_name": user.first_name, 
        "action": action_text, "timestamp": datetime.now().isoformat()
    }
    database['action_log'].insert(0, log_entry)
    database['action_log'] = database['action_log'][:1000]
    await save_database()

def is_admin(user_id: int) -> bool:
    return user_id in ADMIN_IDS

async def log_system_action(text: str, keyboard: InlineKeyboardMarkup = None):
    log_message = f"<b>[SYSTEM]</b> {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n{text}"
    for admin_id in ADMIN_IDS:
        try: 
            await bot.send_message(admin_id, log_message, reply_markup=keyboard)
        except Exception as e: 
            logging.warning(f"Не удалось отправить системный лог админу {admin_id}: {e}")

async def safe_edit_message(call: CallbackQuery, text: str, keyboard: InlineKeyboardMarkup) -> Message | None:
    try:
        if call.message.photo:
            await call.message.delete()
            sent_msg = await call.message.answer(text, reply_markup=keyboard)
            asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
            return sent_msg
        else:
            return await call.message.edit_text(text, reply_markup=keyboard)
    except TelegramBadRequest as e:
        if "message is not modified" in str(e):
            await call.answer()
        elif "message to delete not found" in str(e) or "message to edit not found" in str(e):
            sent_msg = await call.message.answer(text, reply_markup=keyboard)
            asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
            return sent_msg
        else:
            logging.warning(f"Не удалось отредактировать сообщение: {e}. Отправляю новое.")
            try:
                sent_msg = await call.message.answer(text, reply_markup=keyboard)
                asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
                await call.message.delete()
                return sent_msg
            except TelegramBadRequest: pass
    return None

def get_main_menu_keyboard(user_id: int, chat_type: str) -> InlineKeyboardMarkup:
    buttons = [
        [InlineKeyboardButton(text="📊 Общая статистика", callback_data="show_stats")],
        [InlineKeyboardButton(text="📋 Все сделки", callback_data="navigate_trades:1")],
        [InlineKeyboardButton(text="💡 Симуляция", callback_data="simulation_prompt")],
        [InlineKeyboardButton(text="❓ Помощь", callback_data="show_help")],
        [InlineKeyboardButton(text="✍️ Сообщить об ошибке", url=f"https://t.me/{ADMIN_TELEGRAM_USERNAME}")]
    ]
    is_private_chat = chat_type == "private"
    if is_admin(user_id) and is_private_chat:
        buttons.append([InlineKeyboardButton(text="👑 Админ-панель", callback_data="admin_panel")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def get_admin_panel_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📖 Журнал действий", callback_data="view_log:1"), InlineKeyboardButton(text="👥 Пользователи", callback_data="view_users:1")],
        [InlineKeyboardButton(text="🚦 Лимиты", callback_data="view_limits:1"), InlineKeyboardButton(text="📈 Статистика бота", callback_data="bot_stats")],
        [InlineKeyboardButton(text="🔄 Обновить кэш", callback_data="refresh_cache"), InlineKeyboardButton(text="📝 Обновить stats.txt", callback_data="update_stats_prompt")],
        [InlineKeyboardButton(text="📄 Получить stats.txt", callback_data="get_stats_file"), InlineKeyboardButton(text="🧮 Рассчитать движение", callback_data="calculate_movement_start")],
        [InlineKeyboardButton(text="🔍 Проверить статистику", callback_data="check_stats"), InlineKeyboardButton(text="📜 Логи ошибок", callback_data="view_error_log")],
        [InlineKeyboardButton(text="📤 Экспорт БД", callback_data="export_db"), InlineKeyboardButton(text="📥 Импорт БД", callback_data="import_db_prompt")],
        [InlineKeyboardButton(text="💬 Рассылка (ЛС)", callback_data="broadcast_prompt"), InlineKeyboardButton(text="📮 Рассылка (Группы)", callback_data="group_broadcast_prompt")],
        [InlineKeyboardButton(text="⬅️ Назад в меню", callback_data="main_menu")]
    ])

def get_back_keyboard(callback_data="main_menu") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="⬅️ Назад", callback_data=callback_data)]])

async def show_main_menu(message: Message):
    await delete_context_message(message.from_user.id, message.chat.id)
    await log_user_action(message.from_user, f"Вызвал команду {message.text}")
    
    user_mention = get_user_mention(message.from_user)
    text = f"👋 <b>Привет, {user_mention}!</b>\n\nЯ бот для отслеживания статистики. Используйте кнопки ниже для навигации."
    
    sent_msg = await message.answer(text, reply_markup=get_main_menu_keyboard(message.from_user.id, message.chat.type))
    message_owners[sent_msg.message_id] = message.from_user.id
    
    if message.chat.type == "private":
        try:
            await bot.pin_chat_message(message.chat.id, sent_msg.message_id, disable_notification=True)
        except TelegramBadRequest as e:
            logging.warning(f"Не удалось закрепить сообщение в чате {message.chat.id}: {e}")

    asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))
    try:
        await message.delete()
    except TelegramBadRequest:
        pass

@dp.message(CommandStart())
async def command_start_handler(message: Message, state: FSMContext):
    await state.clear()
    await show_main_menu(message)

@dp.message(Command("stat", "help"))
async def command_stat_help_handler(message: Message, state: FSMContext):
    await state.clear()
    if message.text.startswith("/help"):
        await cq_show_help(message)
    else:
        await show_main_menu(message)

@dp.callback_query(F.data == "main_menu")
async def cq_main_menu(call: CallbackQuery, state: FSMContext):
    await delete_context_message(call.from_user.id, call.message.chat.id)
    await state.clear()
    
    user_mention = get_user_mention(call.from_user)
    text = f"👋 <b>Привет, {user_mention}!</b>\n\nЯ бот для отслеживания статистики. Используйте кнопки ниже для навигации."
    
    try: await call.message.delete()
    except TelegramBadRequest: pass
    
    sent_msg = await call.message.answer(text, reply_markup=get_main_menu_keyboard(call.from_user.id, call.message.chat.type))
    message_owners[sent_msg.message_id] = call.from_user.id
    asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))

@dp.callback_query(F.data == "show_help")
async def cq_show_help(event: CallbackQuery | Message):
    text = (
        "<b>❓ Помощь по боту</b>\n\n"
        "Я помогу вам анализировать статистику трейдинга.\n\n"
        "<b>Основные разделы:</b>\n"
        "📊 <b>Общая статистика</b> — ключевые показатели: винрейт, чистое движение, количество сделок и их соотношение.\n\n"
        "📋 <b>Все сделки</b> — полный список всех сделок с детальной информацией по каждой. Включает интерактивный график изменения PnL.\n\n"
        "💡 <b>Симуляция</b> — мощный инструмент для анализа. Позволяет рассчитать, как бы изменился ваш депозит, если бы вы торговали по этой статистике с определенным риском и плечом. Есть три режима:\n"
        "  - <i>Сложный %</i>: риск рассчитывается от текущего баланса.\n"
        "  - <i>Простой %</i>: риск рассчитывается от начального баланса.\n"
        "  - <i>Кастомная</i>: вы можете задать свои параметры.\n\n"
        "✍️ <b>Сообщить об ошибке</b> — прямая связь с администратором для сообщений о багах или опечатках в статистике."
    )
    keyboard = get_back_keyboard("main_menu")
    
    if isinstance(event, CallbackQuery):
        await log_user_action(event.from_user, "Помощь")
        sent_msg = await safe_edit_message(event, text, keyboard)
        if sent_msg: message_owners[sent_msg.message_id] = event.from_user.id
    else:
        await log_user_action(event.from_user, "Помощь")
        await delete_context_message(event.from_user.id, event.chat.id)
        try: await event.delete()
        except TelegramBadRequest: pass
        sent_msg = await event.answer(text, reply_markup=keyboard)
        message_owners[sent_msg.message_id] = event.from_user.id
        asyncio.create_task(delete_message_after_delay(sent_msg, event.chat.type))


@dp.callback_query(F.data == "show_stats")
async def cq_show_stats(call: CallbackQuery):
    await call.answer()
    await delete_context_message(call.from_user.id, call.message.chat.id)
    await log_user_action(call.from_user, "Общая статистика")
    
    summary = STATS_CACHE.get("summary", {})
    png_buf = STATS_CACHE.get("summary_chart_png")
    streaks = STATS_CACHE.get("streaks", {})
    
    if not summary:
        sent_msg = await safe_edit_message(call, "❌ Ошибка: не удалось загрузить данные статистики. Проверьте формат файла `stats.txt`.", get_back_keyboard("main_menu"))
        if sent_msg: message_owners[sent_msg.message_id] = call.from_user.id
        return

    user_mention = get_user_mention(call.from_user)
    text = (f"{user_mention}, вот <b>общая статистика</b>\n"
            f"(с {summary.get('start_date', 'N/A')} по {summary.get('last_update', 'N/A')})\n\n"
            f"🔄 <b>Чистое движение:</b> <code>{summary.get('total_pnl', 'N/A')}</code>\n"
            f"🎯 <b>Винрейт:</b> <code>{summary.get('winrate', 'N/A')}</code>\n\n"
            f"<b>Всего сделок:</b> <code>{summary.get('total_deals', 'N/A')}</code>\n"
            f"🟢 Успешных: <code>{summary.get('successful', 'N/A')}</code>\n"
            f"🔴 Убыточных: <code>{summary.get('losing', 'N/A')}</code>\n"
            f"⚪️ В безубыток: <code>{summary.get('breakeven', 'N/A')}</code>\n\n"
            f"🔥 <b>Макс. серии:</b>\n"
            f"  - В плюс: <code>{streaks.get('win', 0)}</code>\n"
            f"  - В минус: <code>{streaks.get('loss', 0)}</code>\n"
            f"  - В Б/У: <code>{streaks.get('be', 0)}</code>")
    
    try: await call.message.delete()
    except TelegramBadRequest: pass

    if png_buf:
        png_buf.seek(0)
        photo_file = BufferedInputFile(png_buf.read(), "summary.png")
        sent_msg = await call.message.answer_photo(photo=photo_file, caption=text, reply_markup=get_back_keyboard("main_menu"))
        message_owners[sent_msg.message_id] = call.from_user.id
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
    else:
        sent_msg = await call.message.answer(text + "\n\n<i>(Не удалось сгенерировать график)</i>", reply_markup=get_back_keyboard("main_menu"))
        message_owners[sent_msg.message_id] = call.from_user.id
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))


@dp.callback_query(F.data.startswith("navigate_trades:"))
async def cq_navigate_trades(call: CallbackQuery):
    await call.answer()
    await log_user_action(call.from_user, "Все сделки")
    
    page = int(call.data.split(':')[1])
    trades = STATS_CACHE.get("trades", [])
    if not trades:
        sent_msg = await safe_edit_message(call, "Сделок пока нет.", get_back_keyboard("main_menu"))
        if sent_msg: message_owners[sent_msg.message_id] = call.from_user.id
        return
    
    sorted_trades = sorted([t for t in trades if 'date_dt' in t], key=lambda x: x['date_dt'], reverse=True)
    
    total_pages = math.ceil(len(sorted_trades) / ITEMS_PER_PAGE) or 1
    page = max(1, min(page, total_pages))
    
    trades_on_page = sorted_trades[(page - 1) * ITEMS_PER_PAGE:page * ITEMS_PER_PAGE]
    
    user_mention = get_user_mention(call.from_user)
    page_text = f"{user_mention}, вот <b>список сделок (Стр. {page}/{total_pages})</b>\n\n"
    for trade in trades_on_page:
        pnl_value = trade.get('pnl_value', 0)
        icon = "🟢" if pnl_value > 0 else "🔴" if pnl_value < 0 else "⚪️"
        if trade.get('in_progress'): icon = "🔄"
        direction = "▲ Long" if trade.get('type') == 'long' else "▼ Short"
        page_text += (f"<b>{html.quote(trade.get('ticker', 'N/A'))}</b> ({direction}) - <code>{html.quote(trade.get('date', 'N/A'))}</code>\n"
                      f"{icon} PnL: <code>{html.quote(trade.get('pnl', 'N/A'))}</code> | Маржа: <code>{html.quote(trade.get('margin', 'N/A'))}</code>\n"
                      f"ENTRY: <code>{html.quote(trade.get('entry', 'N/A'))}</code>\n"
                      f"Фиксации: <code>{html.quote(trade.get('exits', 'б/у'))}</code>\n--------------------\n")
    
    nav = []
    if page > 1: nav.append(InlineKeyboardButton(text="⬅️", callback_data=f"navigate_trades:{page-1}"))
    nav.append(InlineKeyboardButton(text=f"{page}/{total_pages}", callback_data="noop"))
    if page < total_pages: nav.append(InlineKeyboardButton(text="➡️", callback_data=f"navigate_trades:{page+1}"))
    
    keyboard = InlineKeyboardMarkup(inline_keyboard=[nav, [InlineKeyboardButton(text="⬅️ Назад в меню", callback_data="main_menu")]])

    chat_id = call.message.chat.id
    user_id = call.from_user.id

    if page == 1:
        png_buf = STATS_CACHE.get("pnl_chart_png")
        html_buf = STATS_CACHE.get("pnl_chart_html")

        if not png_buf or not html_buf:
            logging.error("Графики PnL не найдены в кэше для страницы 1.")
            sent_msg = await safe_edit_message(call, page_text, keyboard)
            if sent_msg: message_owners[sent_msg.message_id] = user_id
            return

        try: await call.message.delete()
        except TelegramBadRequest: pass
        await delete_context_message(user_id, chat_id)

        html_buf.seek(0)
        file_doc = BufferedInputFile(html_buf.read(), "interactive_pnl.html")
        file_msg = await bot.send_document(chat_id, file_doc, caption="📄 Интерактивный график PnL")
        await save_context_message(user_id, file_msg.message_id) 
        
        png_buf.seek(0)
        photo_doc = BufferedInputFile(png_buf.read(), "pnl.png")
        sent_msg = await bot.send_photo(chat_id, photo=photo_doc, caption=page_text, reply_markup=keyboard)
        
        message_owners[sent_msg.message_id] = user_id
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
    else:
        sent_msg = await safe_edit_message(call, page_text, keyboard)
        if sent_msg: message_owners[sent_msg.message_id] = user_id

@dp.callback_query(F.data == "simulation_prompt")
async def cq_simulation_prompt(call: CallbackQuery, state: FSMContext):
    await delete_context_message(call.from_user.id, call.message.chat.id)
    await state.clear()
    await log_user_action(call.from_user, "Симуляция")
    
    user_mention = get_user_mention(call.from_user)
    text = f"{user_mention},\n⚙️ Выберите тип симуляции:"
    
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Сложный процент", callback_data="run_simulation:compound")],
        [InlineKeyboardButton(text="Простой процент", callback_data="run_simulation:simple")],
        [InlineKeyboardButton(text="🎨 Кастомная симуляция", callback_data="custom_simulation_start")],
        [InlineKeyboardButton(text="⬅️ Назад", callback_data="main_menu")]
    ])
    sent_msg = await safe_edit_message(call, text, keyboard)
    if sent_msg: message_owners[sent_msg.message_id] = call.from_user.id

def format_simulation_results(sim_type_text, results, initial_balance, risk_percent, leverage):
    final_label = "Итоговая прибыль" if results['final_percent'] >= 0 else "Итоговый убыток"
    x_depo_str = f"{(results['final_balance'] / initial_balance):.2f}x" if initial_balance > 0 else "N/A"
    
    return (f"💡 <b>Результаты симуляции ({sim_type_text})</b>\n\n"
            f"📈 Максимальная прибыль: <code>{results['max_percent']:.2f}%</code>\n"
            f"📉 Максимальный убыток: <code>{results['min_percent']:.2f}%</code>\n\n"
            f"🏁 <b>{final_label}:</b> <code>{results['final_percent']:.2f}%</code>\n\n"
            f"<blockquote><b>Итог:</b>\n"
            f"  - Начальный баланс: <code>${initial_balance:,.0f}</code>\n"
            f"  - Риск на сделку: <code>{risk_percent:.2f}%</code>\n"
            f"  - Кредитное плечо: <code>x{leverage}</code>\n"
            f"  - Множитель к депозиту: <b>{x_depo_str}</b>\n"
            f"  - Итоговый баланс: <code>${results['final_balance']:,.0f}</code></blockquote>")

async def handle_simulation(call: CallbackQuery, sim_type: str, results_key: str, chart_html_key: str, chart_png_key: str, balance: float, risk: float, leverage: float):
    await call.answer()
    await delete_context_message(call.from_user.id, call.message.chat.id)
    
    type_text = "Сложный процент" if sim_type == "compound" else "Простой процент"
    await log_user_action(call.from_user, f"Симуляция ({type_text})")
    
    results = STATS_CACHE.get(results_key)
    html_buf = STATS_CACHE.get(chart_html_key)
    png_buf = STATS_CACHE.get(chart_png_key)
    
    if not all([results, html_buf, png_buf]):
        sent_msg = await safe_edit_message(call, "Ошибка: данные для симуляции не найдены в кэше. Попробуйте обновить кэш.", get_back_keyboard("simulation_prompt"))
        if sent_msg: message_owners[sent_msg.message_id] = call.from_user.id
        return
        
    user_mention = get_user_mention(call.from_user)
    result_text = f"{user_mention}, вот ваши результаты:\n\n" + format_simulation_results(type_text, results, balance, risk, leverage)
    
    chat_id = call.message.chat.id
    user_id = call.from_user.id

    try: await call.message.delete()
    except TelegramBadRequest: pass

    html_buf.seek(0)
    file_doc = BufferedInputFile(html_buf.read(), f"interactive_sim_{sim_type}.html")
    file_msg = await bot.send_document(chat_id, file_doc, caption=f"📄 Интерактивный график ({type_text})")
    await save_context_message(user_id, file_msg.message_id)
    
    png_buf.seek(0)
    photo_doc = BufferedInputFile(png_buf.read(), f"sim_{sim_type}.png")
    sent_msg = await bot.send_photo(chat_id, photo_doc, caption=result_text, reply_markup=get_back_keyboard("simulation_prompt"))
    
    message_owners[sent_msg.message_id] = user_id
    asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))

@dp.callback_query(F.data == "run_simulation:compound")
async def cq_run_sim_compound(call: CallbackQuery, state: FSMContext):
    await handle_simulation(call, "compound", "sim_compound_results", "sim_compound_chart_html", "sim_compound_chart_png", 1000.0, 3.0, 35.0)

@dp.callback_query(F.data == "run_simulation:simple")
async def cq_run_sim_simple(call: CallbackQuery, state: FSMContext):
    await handle_simulation(call, "simple", "sim_simple_results", "sim_simple_chart_html", "sim_simple_chart_png", 1000.0, 3.0, 35.0)

@dp.callback_query(F.data == "custom_simulation_start")
async def cq_custom_simulation_start(call: CallbackQuery, state: FSMContext):
    await delete_context_message(call.from_user.id, call.message.chat.id)
    user_id = call.from_user.id
    
    if not is_admin(user_id):
        used_attempts = get_user_sim_limit(user_id)
        if used_attempts >= CUSTOM_SIM_LIMIT:
            await call.answer(f"Вы достигли лимита в {CUSTOM_SIM_LIMIT} симуляций в сутки.", show_alert=True)
            user_mention = get_user_mention(call.from_user)
            user_info = f"{user_mention} (<code>{user_id}</code>)"
            text = f"⚠️ Пользователь {user_info} исчерпал лимит на кастомные симуляции."
            keyboard = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="⚙️ Управлять лимитами", callback_data=f"limit_user_menu:{user_id}")]])
            await log_system_action(text, keyboard)
            return
        
        user_data = database['users'].get(str(user_id), {})
        last_sim_time_str = user_data.get('last_sim_time')
        if last_sim_time_str:
            last_sim_time = datetime.fromisoformat(last_sim_time_str)
            if datetime.now() - last_sim_time < timedelta(seconds=CUSTOM_SIM_COOLDOWN_SECONDS):
                await call.answer(f"Пожалуйста, подождите {CUSTOM_SIM_COOLDOWN_SECONDS} секунд перед следующей симуляцией.", show_alert=True)
                return
            
    user_mention = get_user_mention(call.from_user)
    text = f"{user_mention},\n<b>Шаг 1/4:</b> Введите начальный баланс (например, 1000):"
    
    sent_msg = await safe_edit_message(call, text, get_back_keyboard("simulation_prompt"))
    if sent_msg:
        await state.set_state(States.get_balance)
        await state.update_data(prompt_message_id=sent_msg.message_id, chat_id=sent_msg.chat.id)
        message_owners[sent_msg.message_id] = call.from_user.id

async def process_next_sim_step(message: Message, state: FSMContext, new_state: State, prompt_text: str, data_key: str, value: Any):
    state_data = await state.get_data()
    prompt_message_id = state_data.get("prompt_message_id")
    chat_id = state_data.get("chat_id")

    try: await message.delete()
    except TelegramBadRequest: pass
        
    if not prompt_message_id or not chat_id:
        await state.clear()
        return

    await state.update_data({data_key: value})
    await state.set_state(new_state)
    
    user_mention = get_user_mention(message.from_user)
    await bot.edit_message_text(f"{user_mention},\n{prompt_text}", chat_id=chat_id, message_id=prompt_message_id, reply_markup=get_back_keyboard("simulation_prompt"))

async def handle_invalid_fsm_input(message: Message, state: FSMContext, error_text: str):
    state_data = await state.get_data()
    prompt_message_id = state_data.get("prompt_message_id")
    chat_id = state_data.get("chat_id")
    
    try: await message.delete()
    except TelegramBadRequest: pass

    if prompt_message_id and chat_id:
        original_prompt = "Пожалуйста, введите данные:" 
        try:
             original_prompt = state_data.get("original_prompt_text", original_prompt)
        except Exception: pass

        user_mention = get_user_mention(message.from_user)
        await bot.edit_message_text(
            f"{user_mention},\n{original_prompt}\n\n<b>❌ Ошибка:</b> {error_text}",
            chat_id=chat_id,
            message_id=prompt_message_id,
            reply_markup=get_back_keyboard("simulation_prompt")
        )

@dp.message(StateFilter(States.get_balance))
async def process_balance(message: Message, state: FSMContext):
    try:
        value = float(message.text.replace(',', '.'))
        if value <= 0: raise ValueError
        await state.update_data(original_prompt_text="<b>Шаг 2/4:</b> Баланс принят! Теперь введите риск на сделку в % (например, 3):")
        await process_next_sim_step(message, state, States.get_risk, "<b>Шаг 2/4:</b> Баланс принят! Теперь введите риск на сделку в % (например, 3):", "balance", value)
    except (ValueError, TypeError):
        await handle_invalid_fsm_input(message, state, "введите корректное положительное число.")

@dp.message(StateFilter(States.get_risk))
async def process_risk(message: Message, state: FSMContext):
    try:
        value = float(message.text.replace(',', '.'))
        if not (0 < value <= 100): raise ValueError
        await state.update_data(original_prompt_text="<b>Шаг 3/4:</b> Риск принят! Введите кредитное плечо (например, 35):")
        await process_next_sim_step(message, state, States.get_leverage, "<b>Шаг 3/4:</b> Риск принят! Введите кредитное плечо (например, 35):", "risk", value)
    except (ValueError, TypeError):
        await handle_invalid_fsm_input(message, state, "введите число от 0 до 100.")

@dp.message(StateFilter(States.get_leverage))
async def process_leverage(message: Message, state: FSMContext):
    try:
        value = float(message.text.replace(',', '.'))
        if value <= 0: raise ValueError
        
        state_data = await state.get_data()
        prompt_message_id = state_data.get("prompt_message_id")
        chat_id = state_data.get("chat_id")
        
        try: await message.delete()
        except TelegramBadRequest: pass
            
        if not prompt_message_id or not chat_id:
            await state.clear()
            return
            
        await state.update_data(leverage=value)
        await state.set_state(States.get_sim_type)
        
        user_mention = get_user_mention(message.from_user)
        text = f"{user_mention},\n<b>Шаг 4/4:</b> Все данные приняты. Выберите тип расчета:"
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Сложный процент", callback_data="custom_sim_run:compound")],
            [InlineKeyboardButton(text="Простой процент", callback_data="custom_sim_run:simple")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="simulation_prompt")]
        ])
        await bot.edit_message_text(text, chat_id=chat_id, message_id=prompt_message_id, reply_markup=keyboard)

    except (ValueError, TypeError):
        await handle_invalid_fsm_input(message, state, "введите корректное положительное число.")

@dp.callback_query(F.data.startswith("custom_sim_run:"), StateFilter(States.get_sim_type))
async def cq_custom_sim_run(call: CallbackQuery, state: FSMContext):
    await call.answer()
    
    sim_type = call.data.split(':')[1]
    user_data = await state.get_data()
    balance = user_data.get('balance')
    risk = user_data.get('risk')
    leverage = user_data.get('leverage')
    await state.clear()

    if any(v is None for v in [balance, risk, leverage]):
        await safe_edit_message(call, "❌ Произошла ошибка, данные были утеряны. Попробуйте снова.", get_back_keyboard("simulation_prompt"))
        return
    
    await call.message.edit_text("⏳ Считаю вашу симуляцию...")
    
    type_text = "Сложный процент" if sim_type == "compound" else "Простой процент"
    log_text = f"Кастомная симуляция ({type_text}): Баланс ${balance}, Риск {risk}%, Плечо x{leverage}"
    await log_user_action(call.from_user, log_text)

    trades = STATS_CACHE.get("trades", [])
    results = await calculate_simulation(trades, sim_type, balance, risk, leverage)
    html_buf, png_buf = await plot_simulation_chart(results['history'])
    
    user_mention = get_user_mention(call.from_user)
    result_text = f"{user_mention}, вот ваша кастомная симуляция:\n\n" + format_simulation_results(f"{type_text} (кастомный)", results, balance, risk, leverage)
    
    chat_id = call.message.chat.id
    user_id = call.from_user.id

    try: await call.message.delete()
    except TelegramBadRequest: pass

    if html_buf and png_buf:
        html_buf.seek(0)
        file_doc = BufferedInputFile(html_buf.read(), "interactive_custom_sim.html")
        file_msg = await bot.send_document(chat_id, file_doc, caption="📄 Интерактивный график кастомной симуляции")
        await save_context_message(user_id, file_msg.message_id)
        
        png_buf.seek(0)
        photo_doc = BufferedInputFile(png_buf.read(), "custom_sim.png")
        sent_msg = await bot.send_photo(chat_id, photo_doc, caption=result_text, reply_markup=get_back_keyboard("simulation_prompt"))
        
        message_owners[sent_msg.message_id] = user_id
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
    else:
        sent_msg = await call.message.answer("❌ Ошибка: не удалось сгенерировать график для кастомной симуляции.", reply_markup=get_back_keyboard("simulation_prompt"))
        message_owners[sent_msg.message_id] = user_id
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))

    if not is_admin(call.from_user.id):
        await increment_user_sim_limit(call.from_user.id)
        database['users'][str(user_id)]['last_sim_time'] = datetime.now().isoformat()
        await save_database()

@dp.callback_query(F.data == "admin_panel")
async def cq_admin_panel(call: CallbackQuery, state: FSMContext):
    if call.message.chat.type != "private":
        return await call.answer("Админ-панель доступна только в личных сообщениях.", show_alert=True)
    if not is_admin(call.from_user.id): return await call.answer("Доступ запрещен", show_alert=True)
    await delete_context_message(call.from_user.id, call.message.chat.id)
    await state.clear()
    sent_msg = await safe_edit_message(call, "👑 <b>Админ-панель</b>", get_admin_panel_keyboard())
    if sent_msg: message_owners[sent_msg.message_id] = call.from_user.id

@dp.callback_query(F.data == "refresh_cache")
async def cq_refresh_cache(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await call.answer("🔄 Обновляю данные и графики...", show_alert=False)
    await update_stats_cache()
    sent_msg = await call.message.answer("✅ Кэш успешно обновлен.")
    asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))

@dp.callback_query(F.data == "bot_stats")
async def cq_bot_stats(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await delete_context_message(call.from_user.id, call.message.chat.id)
    total = len(database['users'])
    banned = sum(1 for u in database['users'].values() if u.get('is_banned'))
    now = datetime.now()
    active_24h, active_7d, new_today, new_week = 0, 0, 0, 0
    for u in database['users'].values():
        try:
            last_act = datetime.strptime(u['last_activity'], "%Y-%m-%d %H:%M:%S")
            if now - last_act <= timedelta(hours=24): active_24h += 1
            if now - last_act <= timedelta(days=7): active_7d += 1
            first_start = datetime.strptime(u['first_start'], "%Y-%m-%d %H:%M:%S")
            if now.date() == first_start.date(): new_today += 1
            if now - first_start <= timedelta(days=7): new_week += 1
        except (ValueError, KeyError): continue
    stats_text = (f"📈 <b>Статистика бота</b>\n\n" f"👥 Всего: <b>{total}</b>\n" f"🚫 Забанено: <b>{banned}</b>\n\n"
                  f"💡 Активных за 24ч: <b>{active_24h}</b>\n" f"💡 Активных за 7д: <b>{active_7d}</b>\n\n"
                  f"🚀 Новых за сегодня: <b>{new_today}</b>\n" f"🚀 Новых за неделю: <b>{new_week}</b>")
    await safe_edit_message(call, stats_text, get_back_keyboard("admin_panel"))

@dp.callback_query(F.data.startswith("view_log:"))
async def cq_view_log(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await delete_context_message(call.from_user.id, call.message.chat.id)
    page = int(call.data.split(':')[1])
    logs = database.get('action_log', [])
    if not logs: return await safe_edit_message(call, "Журнал действий пуст.", get_back_keyboard("admin_panel"))
    total_pages = math.ceil(len(logs) / LOGS_PER_PAGE) or 1
    page = max(1, min(page, total_pages))
    logs_on_page = logs[(page - 1) * LOGS_PER_PAGE : page * LOGS_PER_PAGE]
    text = f"📖 <b>Журнал действий (Стр. {page}/{total_pages})</b>\n\n"
    for log in logs_on_page:
        user_name = html.quote(log.get('first_name') or f"ID: {log.get('user_id')}")
        action = html.quote(log.get('action'))
        try: timestamp = datetime.fromisoformat(log.get('timestamp')).strftime('%d.%m %H:%M')
        except (TypeError, ValueError): timestamp = "N/A"
        text += f"<b>{user_name}</b>: <i>{action}</i>\n<pre>   {timestamp}</pre>\n\n"
    nav = []
    if page > 1: nav.append(InlineKeyboardButton(text="⬅️", callback_data=f"view_log:{page-1}"))
    nav.append(InlineKeyboardButton(text=f"{page}/{total_pages}", callback_data="noop"))
    if page < total_pages: nav.append(InlineKeyboardButton(text="➡️", callback_data=f"view_log:{page+1}"))
    
    keyboard = InlineKeyboardMarkup(inline_keyboard=[nav, [InlineKeyboardButton(text="🗑️ Очистить Журнал", callback_data="clear_log_prompt")], get_back_keyboard("admin_panel").inline_keyboard[0]])
    await safe_edit_message(call, text, keyboard)

@dp.callback_query(F.data == "clear_log_prompt")
async def cq_clear_log_prompt(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    keyboard = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Да, очистить ✅", callback_data="clear_log_confirm")], [InlineKeyboardButton(text="Отмена ❌", callback_data="view_log:1")]])
    await safe_edit_message(call, "Вы уверены, что хотите полностью очистить журнал действий? Это действие необратимо.", keyboard)

@dp.callback_query(F.data == "clear_log_confirm")
async def cq_clear_log_confirm(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    database['action_log'] = []
    await save_database()
    await log_system_action(f"Администратор @{call.from_user.username} (<code>{call.from_user.id}</code>) очистил журнал действий.")
    await call.answer("Журнал действий успешно очищен.", show_alert=True)
    await cq_view_log(CallbackQuery(id=call.id, from_user=call.from_user, chat_instance=call.chat_instance, message=call.message, data="view_log:1"))

@dp.callback_query(F.data.startswith("view_users:"))
async def cq_view_users(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await delete_context_message(call.from_user.id, call.message.chat.id)
    page = int(call.data.split(':')[1])
    all_users = list(database['users'].items())
    total_pages = math.ceil(len(all_users) / ITEMS_PER_PAGE) or 1
    page = max(1, min(page, total_pages))
    users_on_page = all_users[(page - 1) * ITEMS_PER_PAGE:page * ITEMS_PER_PAGE]
    text = "👥 <b>Список пользователей</b>\n\n"
    keyboard_builder = []
    for uid, u_data in users_on_page:
        ban_status = "🚫" if u_data.get('is_banned') else "✅"
        name = html.quote(f"@{u_data['username']}" if u_data.get('username') else u_data.get('first_name', f"User {uid}"))
        text += f"{ban_status} {name} (<code>{uid}</code>)\n   <i>Старт: {u_data.get('first_start', 'N/A')}</i>\n\n"
        keyboard_builder.append([InlineKeyboardButton(text=name, callback_data=f"user_profile:{uid}")])
    nav = []
    if page > 1: nav.append(InlineKeyboardButton(text="◀️", callback_data=f"view_users:{page-1}"))
    nav.append(InlineKeyboardButton(text=f"{page}/{total_pages}", callback_data="noop"))
    if page < total_pages: nav.append(InlineKeyboardButton(text="▶️", callback_data=f"view_users:{page+1}"))
    if len(all_users) > ITEMS_PER_PAGE: keyboard_builder.append(nav)
    keyboard_builder.append([InlineKeyboardButton(text="🔍 Поиск", callback_data="search_user_prompt")])
    keyboard_builder.append(get_back_keyboard("admin_panel").inline_keyboard[0])
    await safe_edit_message(call, text, InlineKeyboardMarkup(inline_keyboard=keyboard_builder))

@dp.callback_query(F.data.startswith("user_profile:"))
async def cq_user_profile(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await delete_context_message(call.from_user.id, call.message.chat.id)
    target_id_str = call.data.split(':')[1]
    await send_user_profile(call, target_id_str)

async def send_user_profile(event: Message | CallbackQuery, target_id_str: str):
    user_data = database['users'].get(target_id_str)
    if not user_data:
        text = "Пользователь не найден."
        if isinstance(event, CallbackQuery): 
            await event.answer(text, show_alert=True)
            await cq_view_users(CallbackQuery(id=event.id, from_user=event.from_user, chat_instance=event.chat_instance, message=event.message, data="view_users:1"))
        else: 
            sent_msg = await event.answer(text)
            asyncio.create_task(delete_message_after_delay(sent_msg, event.chat.type))
        return

    ban_status = "🚫 Забанен" if user_data.get('is_banned') else "✅ Активен"
    username = f"@{user_data['username']}" if user_data.get('username') else "Нет"
    profile_text = (f"👤 <b>Профиль:</b> {html.quote(user_data.get('first_name', ''))}\n\n"
                    f"<b>ID:</b> <code>{target_id_str}</code>\n" f"<b>Юзернейм:</b> {html.quote(username)}\n"
                    f"<b>Статус:</b> {ban_status}\n\n" f"<b>Первый запуск:</b> {user_data.get('first_start', 'N/A')}\n"
                    f"<b>Активность:</b> {user_data.get('last_activity', 'N/A')}\n" f"<b>Сообщений:</b> {user_data.get('message_count', 0)}\n")
    
    ban_text = "✅ Разбанить" if user_data.get('is_banned') else "🚫 Забанить"
    ban_cb = f"unban_user:{target_id_str}" if user_data.get('is_banned') else f"ban_user:{target_id_str}"
    
    keyboard_buttons = []
    if int(target_id_str) != FOUNDER_ID:
        keyboard_buttons.append([InlineKeyboardButton(text=ban_text, callback_data=ban_cb)])
    
    keyboard_buttons.append(get_back_keyboard("view_users:1").inline_keyboard[0])
    keyboard = InlineKeyboardMarkup(inline_keyboard=keyboard_buttons)
    
    if isinstance(event, CallbackQuery):
        await safe_edit_message(event, profile_text, keyboard)
    else: 
        try:
            await event.delete()
        except TelegramBadRequest:
            logging.warning(f"Не удалось удалить сообщение {event.message_id} в send_user_profile")
        sent_msg = await event.answer(profile_text, reply_markup=keyboard)
        asyncio.create_task(delete_message_after_delay(sent_msg, event.chat.type))

@dp.callback_query(F.data.startswith(("ban_user:", "unban_user:")))
async def cq_ban_unban_user(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    action, target_id_str = call.data.split(':')
    if int(target_id_str) == FOUNDER_ID: return await call.answer("Нельзя изменить статус основателя.", show_alert=True)
    user_data = database['users'].get(target_id_str)
    if not user_data: return await call.answer("Пользователь не найден.", show_alert=True)
    is_banning = action == "ban_user"
    user_data['is_banned'] = is_banning
    await save_database()
    await call.answer(f"Пользователь {'забанен' if is_banning else 'разбанен'}.")
    try:
        text = f"Ваш аккаунт был заблокирован. Обратитесь: @{ADMIN_TELEGRAM_USERNAME}" if is_banning else "Ваш аккаунт был разблокирован."
        sent_msg = await bot.send_message(target_id_str, text)
        asyncio.create_task(delete_message_after_delay(sent_msg, "private"))
    except Exception as e: logging.warning(f"Не удалось уведомить {target_id_str}: {e}")
    await send_user_profile(call, target_id_str)

@dp.callback_query(F.data == "search_user_prompt")
async def cq_search_user_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.set_state(States.get_search_query)
    await safe_edit_message(call, "Введите ID, юзернейм или имя для поиска:", get_back_keyboard("view_users:1"))

@dp.message(StateFilter(States.get_search_query))
async def process_user_search(message: Message, state: FSMContext):
    await state.clear()
    query = message.text.strip().lower()
    
    found_users = []
    if query.isdigit():
        if query in database['users']:
            found_users.append((query, database['users'][query]))
    
    if not found_users:
        for uid, u_data in database['users'].items():
            username = u_data.get('username', '').lower()
            first_name = u_data.get('first_name', '').lower()
            
            if query in username or query in first_name:
                found_users.append((uid, u_data))

    try: await message.delete()
    except TelegramBadRequest: pass

    if not found_users:
        sent_msg = await message.answer(f"❌ Пользователь по запросу <code>{html.quote(query)}</code> не найден.", reply_markup=get_back_keyboard("view_users:1"))
        asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))
    elif len(found_users) == 1:
        await send_user_profile(message, found_users[0][0])
    else:
        text = "Найдено несколько пользователей. Выберите нужного:"
        keyboard_builder = []
        for uid, u_data in found_users[:20]:
            name = html.quote(f"@{u_data['username']}" if u_data.get('username') else u_data.get('first_name', f"User {uid}"))
            keyboard_builder.append([InlineKeyboardButton(text=f"{name} ({uid})", callback_data=f"user_profile:{uid}")])
        keyboard_builder.append(get_back_keyboard("view_users:1").inline_keyboard[0])
        sent_msg = await message.answer(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=keyboard_builder))
        asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))

@dp.callback_query(F.data == "view_error_log")
async def cq_view_error_log(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    LOG_LINES_TO_SHOW = 25
    try:
        with open(LOG_FILE, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        last_lines = lines[-LOG_LINES_TO_SHOW:]
        if not last_lines:
            text = "Файл логов пуст."
        else:
            log_content = "".join(last_lines)
            text = f"Последние {len(last_lines)} строк из <code>{LOG_FILE}</code>:\n\n<pre>{html.quote(log_content)}</pre>"
        
        await safe_edit_message(call, text, get_back_keyboard("admin_panel"))
    except FileNotFoundError:
        await safe_edit_message(call, f"Файл логов <code>{LOG_FILE}</code> не найден.", get_back_keyboard("admin_panel"))
    except Exception as e:
        await safe_edit_message(call, f"Ошибка чтения логов: {e}", get_back_keyboard("admin_panel"))

@dp.callback_query(F.data == "export_db")
async def cq_export_db(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    db_string = json.dumps(database, indent=4, ensure_ascii=False)
    db_file = BufferedInputFile(db_string.encode('utf-8'), filename=f'db_backup_{datetime.now().strftime("%Y-%m-%d_%H-%M")}.json')
    await call.message.answer_document(db_file, caption="Резервная копия базы данных.")
    await call.answer("Файл отправлен.")

@dp.callback_query(F.data == "import_db_prompt")
async def cq_import_db_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    text = "Вы уверены, что хотите импортировать новую базу данных? <b>Текущая БД будет полностью заменена.</b> Это действие необратимо."
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Да, я понимаю", callback_data="import_db_confirm")],
        [InlineKeyboardButton(text="Отмена", callback_data="admin_panel")]
    ])
    await safe_edit_message(call, text, keyboard)

@dp.callback_query(F.data == "import_db_confirm")
async def cq_import_db_confirm(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.set_state(States.get_import_file)
    await safe_edit_message(call, "Пришлите файл <code>.json</code> для импорта.", get_back_keyboard("admin_panel"))

@dp.message(StateFilter(States.get_import_file), F.document)
async def handle_db_import(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    if message.document.mime_type == 'application/json':
        try:
            file = await bot.get_file(message.document.file_id)
            file_content = await bot.download_file(file.file_path)
            new_db = json.loads(file_content.read())
            if 'users' in new_db and 'admins' in new_db:
                global database
                database = new_db
                if FOUNDER_ID not in database['admins']: database['admins'].append(FOUNDER_ID)
                if 'action_log' not in database: database['action_log'] = []
                await save_database()
                sent_msg = await message.reply("✅ База данных успешно импортирована.")
                asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))
            else: 
                sent_msg = await message.reply("❌ Ошибка: структура файла неверна.")
                asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))
        except Exception as e: 
            sent_msg = await message.reply(f"❌ Произошла ошибка при импорте: {e}")
            asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))
        finally: await state.clear()
    else: 
        sent_msg = await message.reply("❌ Пришлите файл с расширением .json")
        asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))
    asyncio.create_task(delete_message_after_delay(message, message.chat.type))

@dp.callback_query(F.data == "update_stats_prompt")
async def cq_update_stats_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.set_state(States.update_stats_file)
    await safe_edit_message(call, "Отправьте новый файл `stats.txt` для обновления.", get_back_keyboard("admin_panel"))

@dp.message(StateFilter(States.update_stats_file), F.document)
async def handle_stats_update(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id): return
    if not message.document.file_name or not message.document.file_name.endswith('.txt'):
        sent_msg = await message.reply("❌ Ошибка: Файл не принят. Пожалуйста, отправьте файл с расширением `.txt`.", reply_markup=get_back_keyboard("admin_panel"))
        asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))
        asyncio.create_task(delete_message_after_delay(message, message.chat.type))
        return await state.clear()
    try:
        file = await bot.get_file(message.document.file_id)
        file_content_bytes = await bot.download_file(file.file_path)
        file_content = file_content_bytes.read().decode('utf-8')

        temp_summary, temp_trades = await asyncio.to_thread(_parse_stats_data_sync, file_content)
        if not temp_summary and not temp_trades:
             raise ValueError("Не удалось распознать структуру файла. Проверьте формат.")

        await create_stats_backup()
        with open(STATS_FILE, 'w', encoding='utf-8') as f: f.write(file_content)
        
        msg1 = await message.reply("✅ `stats.txt` принят.")
        msg2 = await message.answer("🔄 Обновляю кэш...")
        await update_stats_cache()
        await msg2.edit_text("✅ Кэш обновлен.")
        await msg1.delete()
        await message.delete()
        
        await log_system_action(f"Администратор @{message.from_user.username} (<code>{message.from_user.id}</code>) обновил файл `stats.txt`.")
    except Exception as e:
        logging.error(f"Ошибка обновления stats.txt: {e}")
        sent_msg = await message.reply(f"❌ Произошла критическая ошибка при обновлении файла: {e}", reply_markup=get_back_keyboard("admin_panel"))
        asyncio.create_task(delete_message_after_delay(sent_msg, message.chat.type))
        asyncio.create_task(delete_message_after_delay(message, message.chat.type))
    finally: await state.clear()

@dp.callback_query(F.data == "get_stats_file")
async def cq_get_stats_file(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    try:
        stats_file = BufferedInputFile.from_file(STATS_FILE, filename="stats.txt")
        sent_msg = await call.message.answer_document(stats_file, caption="Последняя версия файла `stats.txt`.")
        await call.answer()
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
    except Exception as e:
        await call.answer("❌ Не удалось отправить файл.", show_alert=True)
        logging.error(f"Ошибка отправки stats.txt: {e}")

@dp.callback_query(F.data == "broadcast_prompt")
async def cq_broadcast_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.set_state(States.get_broadcast_content)
    await safe_edit_message(call, "Отправьте сообщение (текст или фото с подписью) для рассылки пользователям в ЛС.", get_back_keyboard("admin_panel"))

@dp.message(StateFilter(States.get_broadcast_content), F.photo | F.text)
async def process_broadcast_content(message: Message, state: FSMContext):
    admin_id = message.from_user.id
    broadcast_content[admin_id] = message
    keyboard = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Да, отправить ✅", callback_data=f"confirm_broadcast:{admin_id}")], [InlineKeyboardButton(text="Отмена ❌", callback_data="cancel_broadcast")]])
    await message.answer("Вы уверены, что хотите разослать это сообщение всем пользователям в ЛС?", reply_markup=keyboard)
    await state.set_state(States.confirm_broadcast)

@dp.callback_query(F.data.startswith("confirm_broadcast:"), StateFilter(States.confirm_broadcast))
async def cq_confirm_broadcast(call: CallbackQuery, state: FSMContext):
    await state.clear()
    admin_id = int(call.data.split(':')[1])
    content_message = broadcast_content.pop(admin_id, None)
    if not content_message: return await safe_edit_message(call, "Ошибка: сообщение для рассылки не найдено.", get_back_keyboard("admin_panel"))
    
    active_users = [uid for uid, udata in database['users'].items() if not udata.get('is_banned')]
    for uid in active_users:
        await broadcast_queue.put(('copy', uid, content_message.chat.id, content_message.message_id, None))
    
    await call.message.edit_text(f"✅ Рассылка в ЛС для {len(active_users)} пользователей поставлена в очередь.")
    await call.message.answer("👑 <b>Админ-панель</b>", reply_markup=get_admin_panel_keyboard())

@dp.callback_query(F.data == "cancel_broadcast")
async def cq_cancel_broadcast(call: CallbackQuery, state: FSMContext):
    await state.clear()
    await safe_edit_message(call, "Рассылка отменена.", get_back_keyboard("admin_panel"))

@dp.callback_query(F.data == "group_broadcast_prompt")
async def cq_group_broadcast_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.set_state(States.get_group_broadcast_content)
    await safe_edit_message(call, "Отправьте сообщение (текст или фото с подписью) для рассылки по группам.", get_back_keyboard("admin_panel"))

@dp.message(StateFilter(States.get_group_broadcast_content), F.photo | F.text)
async def process_group_broadcast_content(message: Message, state: FSMContext):
    admin_id = message.from_user.id
    broadcast_content[admin_id] = message
    await state.update_data(admin_id=admin_id)
    await state.set_state(States.get_group_broadcast_pin_duration)
    await message.answer("Введите длительность закрепления сообщения в минутах (0 - не закреплять):")

@dp.message(StateFilter(States.get_group_broadcast_pin_duration))
async def process_group_pin_duration(message: Message, state: FSMContext):
    try:
        duration_minutes = int(message.text)
        if duration_minutes < 0: raise ValueError
        
        data = await state.get_data()
        admin_id = data.get('admin_id')
        
        await state.update_data(pin_duration=duration_minutes)
        await state.set_state(States.confirm_group_broadcast)

        text = f"Вы уверены, что хотите разослать это сообщение во все группы?"
        if duration_minutes > 0:
            text += f" и закрепить на {duration_minutes} минут?"
        
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Да, отправить ✅", callback_data=f"confirm_group_broadcast:{admin_id}")],
            [InlineKeyboardButton(text="Отмена ❌", callback_data="cancel_broadcast")]
        ])
        await message.answer(text, reply_markup=keyboard)

    except (ValueError, TypeError):
        await message.reply("❌ Введите корректное целое число.")

@dp.callback_query(F.data.startswith("confirm_group_broadcast:"), StateFilter(States.confirm_group_broadcast))
async def cq_confirm_group_broadcast(call: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    admin_id = int(call.data.split(':')[1])
    pin_duration = data.get('pin_duration', 0)
    await state.clear()
    
    content_message = broadcast_content.pop(admin_id, None)
    if not content_message:
        return await safe_edit_message(call, "Ошибка: сообщение для рассылки не найдено.", get_back_keyboard("admin_panel"))

    group_chats = database.get('group_chats', [])
    if not group_chats:
        return await safe_edit_message(call, "Не найдено ни одной группы для рассылки.", get_back_keyboard("admin_panel"))

    for chat_id in group_chats:
        await broadcast_queue.put(('copy_and_pin', chat_id, content_message.chat.id, content_message.message_id, pin_duration * 60))

    await call.message.edit_text(f"✅ Рассылка по {len(group_chats)} группам поставлена в очередь.")
    await call.message.answer("👑 <b>Админ-панель</b>", reply_markup=get_admin_panel_keyboard())

@dp.callback_query(F.data == "calculate_movement_start")
async def cq_calculate_movement_start(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.clear() 
    await state.set_state(States.get_calc_ticker)
    await state.update_data(calc_data={})
    await safe_edit_message(call, "🧮 <b>Калькулятор движения</b>\n\n<b>Шаг 1/5:</b> Введите название монеты (тикер):", get_back_keyboard("admin_panel"))

def _format_calc_prompt(data: dict) -> str:
    text = "🧮 <b>Калькулятор движения</b>\n\n"
    if "ticker" in data: text += f"▪️ Монета: <code>{html.quote(data['ticker'])}</code>\n"
    if "entry" in data: text += f"▪️ Вход: <code>{data['entry']}</code>\n"
    if "margin" in data: text += f"▪️ Маржа: <code>x{data['margin']}</code>\n"
    if "direction" in data: text += f"▪️ Направление: <code>{data['direction'].upper()}</code>\n"
    text += "\n"
    return text

@dp.message(StateFilter(States.get_calc_ticker))
async def process_calc_ticker(message: Message, state: FSMContext):
    data = {"ticker": message.text.upper()}
    await state.update_data(calc_data=data)
    prompt_text = _format_calc_prompt(data) + "<b>Шаг 2/5:</b> Введите точку входа:"
    await message.reply(prompt_text, reply_markup=get_back_keyboard("admin_panel"))
    await state.set_state(States.get_calc_entry)
    await message.delete()

@dp.message(StateFilter(States.get_calc_entry))
async def process_calc_entry(message: Message, state: FSMContext):
    try:
        entry_price = float(message.text.replace(',', '.'))
        if entry_price <= 0: raise ValueError
        data = (await state.get_data()).get('calc_data', {})
        data['entry'] = entry_price
        await state.update_data(calc_data=data)
        prompt_text = _format_calc_prompt(data) + "<b>Шаг 3/5:</b> Введите маржу (например, 1.25 или x20):"
        await message.reply(prompt_text, reply_markup=get_back_keyboard("admin_panel"))
        await state.set_state(States.get_calc_margin)
    except (ValueError, TypeError):
        await message.reply("❌ Ошибка: введите корректное число для цены входа.")
    finally:
        await message.delete()

@dp.message(StateFilter(States.get_calc_margin))
async def process_calc_margin(message: Message, state: FSMContext):
    try:
        margin_text = message.text.lower().replace(',', '.').replace('x', '')
        margin = float(margin_text)
        if margin <= 0: raise ValueError
        data = (await state.get_data()).get('calc_data', {})
        data['margin'] = margin
        await state.update_data(calc_data=data)
        prompt_text = _format_calc_prompt(data) + "<b>Шаг 4/5:</b> Выберите направление:"
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Long", callback_data="calc_direction:long"), InlineKeyboardButton(text="Short", callback_data="calc_direction:short")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="admin_panel")]])
        await message.reply(prompt_text, reply_markup=keyboard)
        await state.set_state(States.get_calc_direction)
    except (ValueError, TypeError):
        await message.reply("❌ Ошибка: введите корректное число для маржи.")
    finally:
        await message.delete()

@dp.callback_query(F.data.startswith("calc_direction:"), StateFilter(States.get_calc_direction))
async def process_calc_direction(call: CallbackQuery, state: FSMContext):
    direction = call.data.split(':')[1]
    data = (await state.get_data()).get('calc_data', {})
    data['direction'] = direction
    await state.update_data(calc_data=data)
    prompt_text = _format_calc_prompt(data) + "<b>Шаг 5/5:</b> Введите фиксации в формате:\n<code>цена (процент%) цена (процент%)</code>"
    await call.message.edit_text(prompt_text, reply_markup=get_back_keyboard("admin_panel"))
    await state.set_state(States.get_calc_exits)

@dp.message(StateFilter(States.get_calc_exits))
async def process_calc_exits(message: Message, state: FSMContext):
    data = (await state.get_data()).get('calc_data', {})
    entry_price = data['entry']
    direction = data['direction']
    margin = data['margin']
    exits_text = message.text
    exits_raw = re.findall(r'([0-9.,]+)\s*\(([\d.]+)%\)', exits_text)
    
    await message.delete()

    if not exits_raw:
        await message.answer("❌ Ошибка: не удалось распознать фиксации. Формат: `цена (процент%)`.", reply_markup=get_back_keyboard("admin_panel"))
        return
    try:
        exits = [(float(price.replace(',', '.')), float(percent)) for price, percent in exits_raw]
        total_percent = sum(p for _, p in exits)
        if total_percent > 100.1:
            await message.answer(f"❌ Ошибка: сумма процентов ({total_percent}%) больше 100.", reply_markup=get_back_keyboard("admin_panel"))
            return
        if total_percent < 99.9: exits.append((entry_price, 100 - total_percent))
        
        net_movement = sum(((p - entry_price) / entry_price * 100 if direction == 'long' else (entry_price - p) / entry_price * 100) * (pct / 100) for p, pct in exits)
        final_pnl = net_movement * margin

        result_text = (f"{data['ticker']} ({direction})\n\n"
                       f"Чистое движение: {final_pnl:.2f}%\n\n"
                       f"ENTRY: {entry_price}\n\n"
                       f"Маржа: X{margin}\n\n"
                       f"Фиксации: {exits_text}\n\n"
                       f"Дата: {datetime.now().strftime('%d.%m.%Y')}")
        
        await state.update_data(final_trade_text=result_text)
        await state.set_state(States.confirm_add_trade_to_stats)
        
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="✅ Добавить в stats.txt", callback_data="add_trade_to_stats")],
            [InlineKeyboardButton(text="⬅️ Назад в админ-панель", callback_data="admin_panel")]
        ])
        await message.answer(f"✅ <b>Результат расчета:</b>\n\n<pre>{html.quote(result_text)}</pre>", reply_markup=keyboard)
        await log_system_action(f"Администратор @{message.from_user.username} рассчитал движение для {data['ticker']}.")
    except (ValueError, TypeError):
        await message.answer("❌ Ошибка: неверный формат чисел в фиксациях.", reply_markup=get_back_keyboard("admin_panel"))
        await state.clear()

@dp.callback_query(F.data == "add_trade_to_stats", StateFilter(States.confirm_add_trade_to_stats))
async def cq_add_trade_to_stats(call: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    trade_text = data.get("final_trade_text")
    await state.clear()

    if not trade_text:
        return await call.answer("Ошибка: данные о сделке утеряны.", show_alert=True)
    
    try:
        await call.message.edit_text("🔄 Добавляю сделку и обновляю статистику...")
        
        with open(STATS_FILE, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        separator = '--- Статистика: Илья Власов - Грабитель ММ ---'
        sep_indices = [i for i, line in enumerate(lines) if separator in line]
        if len(sep_indices) < 2:
            raise ValueError("Неверная структура файла stats.txt")
        
        insert_position = sep_indices[1] + 1
        
        lines.insert(insert_position, f"\n\n\n{trade_text}")
        
        await create_stats_backup()
        with open(STATS_FILE, 'w', encoding='utf-8') as f:
            f.writelines(lines)
        
        await call.message.edit_text("✅ Сделка добавлена. Запускаю авто-обновление шапки...")
        
        await auto_rewrite_stats_header(call)
        
    except Exception as e:
        logging.error(f"Ошибка добавления сделки в stats.txt: {e}")
        await call.message.edit_text(f"❌ Ошибка: {e}", reply_markup=get_back_keyboard("admin_panel"))


@dp.callback_query(F.data == "check_stats")
async def cq_check_stats(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await call.answer("🔍 Проверяю статистику...")

    summary_from_file, trades = await parse_stats_data()
    if not trades:
        sent_msg = await call.message.answer("❌ Не удалось найти сделки в файле `stats.txt` для проверки.", reply_markup=get_back_keyboard("admin_panel"))
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
        return

    completed_trades = [t for t in trades if not t.get('in_progress')]
    in_progress_trades_count = len(trades) - len(completed_trades)
    
    successful = sum(1 for t in completed_trades if t.get('pnl_value', 0) > 0)
    losing = sum(1 for t in completed_trades if t.get('pnl_value', 0) < 0)
    breakeven = len(completed_trades) - successful - losing
    total_deals = len(trades)
    winrate = (successful / (successful + losing) * 100) if (successful + losing) > 0 else 0
    total_pnl = sum(t.get('pnl_value', 0) for t in completed_trades)
    last_trade_date = max(t['date_dt'] for t in trades if 'date_dt' in t) if any(t.get('date_dt') for t in trades) else None
    
    discrepancies = []
    try:
        if abs(float(summary_from_file.get('total_pnl', '0%').replace('%','')) - total_pnl) > 0.01:
            discrepancies.append(f"Чистое движение: <code>{summary_from_file.get('total_pnl')}</code> -> <code>{total_pnl:.2f}%</code>")
        if abs(float(summary_from_file.get('winrate', '0%').replace('%','')) - winrate) > 0.01:
             discrepancies.append(f"Винрейт: <code>{summary_from_file.get('winrate')}</code> -> <code>{winrate:.2f}%</code>")
        if int(summary_from_file.get('total_deals', 0)) != total_deals:
            discrepancies.append(f"Всего сделок: <code>{summary_from_file.get('total_deals')}</code> -> <code>{total_deals}</code>")
        if int(summary_from_file.get('successful', 0)) != successful:
            discrepancies.append(f"Успешных: <code>{summary_from_file.get('successful')}</code> -> <code>{successful}</code>")
        if int(summary_from_file.get('losing', 0)) != losing:
            discrepancies.append(f"Убыточных: <code>{summary_from_file.get('losing')}</code> -> <code>{losing}</code>")
        if int(summary_from_file.get('breakeven', 0)) != breakeven:
            discrepancies.append(f"В безубыток: <code>{summary_from_file.get('breakeven')}</code> -> <code>{breakeven}</code>")
        if int(summary_from_file.get('in_progress', 0)) != in_progress_trades_count:
            discrepancies.append(f"В отработке: <code>{summary_from_file.get('in_progress')}</code> -> <code>{in_progress_trades_count}</code>")
        
        file_update_date_str = summary_from_file.get('last_update')
        if file_update_date_str and last_trade_date:
            file_update_date = datetime.strptime(file_update_date_str, "%d.%m.%y")
            if file_update_date.date() != last_trade_date.date():
                 discrepancies.append(f"Дата обновления: <code>{file_update_date.strftime('%d.%m.%y')}</code> -> <code>{last_trade_date.strftime('%d.%m.%y')}</code>")

    except (ValueError, TypeError, KeyError) as e:
        sent_msg = await call.message.answer(f"❌ Ошибка при сравнении данных: {e}. Проверьте формат шапки в `stats.txt`.", reply_markup=get_back_keyboard("admin_panel"))
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
        return

    if not discrepancies:
        sent_msg = await call.message.answer("✅ Проверка завершена. Расхождений не найдено!", reply_markup=get_back_keyboard("admin_panel"))
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))
    else:
        text = "⚠️ <b>Найдены расхождения в статистике!</b>\n\n" + "\n".join(discrepancies) + "\n\nХотите обновить данные в файле `stats.txt`?"
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Да, обновить ✅", callback_data="confirm_stats_rewrite")],
            [InlineKeyboardButton(text="Отмена ❌", callback_data="admin_panel")]
        ])
        sent_msg = await call.message.answer(text, reply_markup=keyboard)
        asyncio.create_task(delete_message_after_delay(sent_msg, call.message.chat.type))

async def auto_rewrite_stats_header(call: CallbackQuery):
    summary_from_file, trades = await parse_stats_data()
    if not trades:
        return await call.message.edit_text("❌ Ошибка: не удалось прочитать сделки для обновления.", reply_markup=get_back_keyboard("admin_panel"))

    completed_trades = [t for t in trades if not t.get('in_progress')]
    in_progress_trades_count = len(trades) - len(completed_trades)
    
    successful = sum(1 for t in completed_trades if t.get('pnl_value', 0) > 0)
    losing = sum(1 for t in completed_trades if t.get('pnl_value', 0) < 0)
    breakeven = len(completed_trades) - successful - losing
    total_deals = len(trades)
    winrate = (successful / (successful + losing) * 100) if (successful + losing) > 0 else 0
    total_pnl = sum(t.get('pnl_value', 0) for t in completed_trades)
    last_trade_date = max(t['date_dt'] for t in trades if 'date_dt' in t) if any(t.get('date_dt') for t in trades) else datetime.now()

    new_header_content = (
        f"Чистое движение: {total_pnl:.2f}%\n"
        f"Винрейт: {winrate:.2f}%\n"
        f"Всего сделок: {total_deals}\n"
        f"Успешных: {successful}\n"
        f"Убыточных: {losing}\n"
        f"В безубыток: {breakeven}\n"
        f"В отработке: {in_progress_trades_count}\n\n\n"
        f"Начало - {summary_from_file.get('start_date', 'N/A')}\n"
        f"Последнее обновление - {last_trade_date.strftime('%d.%m.%y')}\n"
        f"Если нашли ошибку/опечатку = t.me/{ADMIN_TELEGRAM_USERNAME}"
    )
    
    try:
        with open(STATS_FILE, 'r', encoding='utf-8') as f:
            full_content = f.read()
        
        separator = '--- Статистика: Илья Власов - Грабитель ММ ---'
        new_full_content = re.sub(
            rf"({re.escape(separator)})(.*?)({re.escape(separator)})",
            rf"\1\n{new_header_content}\n\n\n\3",
            full_content,
            count=1,
            flags=re.DOTALL
        )
        await create_stats_backup()
        with open(STATS_FILE, 'w', encoding='utf-8') as f:
            f.write(new_full_content)
        
        await call.message.edit_text("✅ Файл `stats.txt` успешно обновлен. Обновляю кэш...")
        await update_stats_cache()
        await call.message.edit_text("✅ Кэш обновлен!", reply_markup=get_back_keyboard("admin_panel"))
        await log_system_action(f"Администратор @{call.from_user.username} автоматически обновил `stats.txt`.")

    except Exception as e:
        logging.error(f"Критическая ошибка при перезаписи stats.txt: {e}")
        await call.message.edit_text(f"❌ Ошибка при перезаписи файла: {e}", reply_markup=get_back_keyboard("admin_panel"))

@dp.callback_query(F.data == "confirm_stats_rewrite")
async def cq_confirm_stats_rewrite(call: CallbackQuery):
    if not is_admin(call.from_user.id): return
    await call.message.edit_text("🔄 Начинаю обновление файла `stats.txt`...")
    await auto_rewrite_stats_header(call)

@dp.callback_query(F.data.startswith("view_limits:"))
async def cq_view_limits(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.clear()
    page = int(call.data.split(':')[1])
    all_users = list(database['users'].items())
    total_pages = math.ceil(len(all_users) / ITEMS_PER_PAGE) or 1
    page = max(1, min(page, total_pages))
    users_on_page = all_users[(page - 1) * ITEMS_PER_PAGE:page * ITEMS_PER_PAGE]
    text = f"🚦 <b>Управление лимитами (Стр. {page}/{total_pages})</b>\n\n"
    keyboard_builder = []
    for uid, u_data in users_on_page:
        remaining = CUSTOM_SIM_LIMIT - get_user_sim_limit(int(uid))
        name = html.quote(f"@{u_data['username']}" if u_data.get('username') else u_data.get('first_name', f"User {uid}"))
        text += f"👤 {name} (<code>{uid}</code>)\n   <i>Осталось попыток: <b>{remaining}</b></i>\n\n"
        keyboard_builder.append([InlineKeyboardButton(text=f"{name} ({remaining})", callback_data=f"limit_user_menu:{uid}")])
    nav = []
    if page > 1: nav.append(InlineKeyboardButton(text="◀️", callback_data=f"view_limits:{page-1}"))
    nav.append(InlineKeyboardButton(text=f"{page}/{total_pages}", callback_data="noop"))
    if page < total_pages: nav.append(InlineKeyboardButton(text="▶️", callback_data=f"view_limits:{page+1}"))
    if len(all_users) > ITEMS_PER_PAGE: keyboard_builder.append(nav)
    keyboard_builder.append(get_back_keyboard("admin_panel").inline_keyboard[0])
    await safe_edit_message(call, text, InlineKeyboardMarkup(inline_keyboard=keyboard_builder))

@dp.callback_query(F.data.startswith("limit_user_menu:"))
async def cq_limit_user_menu(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    await state.clear()
    user_id = int(call.data.split(':')[1])
    user_data = database['users'].get(str(user_id))
    if not user_data: return await call.answer("Пользователь не найден", show_alert=True)
    name = html.quote(f"@{user_data['username']}" if user_data.get('username') else user_data.get('first_name', f"User {user_id}"))
    remaining = CUSTOM_SIM_LIMIT - get_user_sim_limit(user_id)
    text = f"Что сделать с лимитами для {name}?\nТекущий остаток: {remaining}"
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⚙️ Установить остаток", callback_data=f"set_limit_prompt:{user_id}")],
        [InlineKeyboardButton(text="⬅️ Назад", callback_data="view_limits:1")]
    ])
    await safe_edit_message(call, text, keyboard)

@dp.callback_query(F.data.startswith("set_limit_prompt:"))
async def cq_set_limit_prompt(call: CallbackQuery, state: FSMContext):
    if not is_admin(call.from_user.id): return
    user_id = int(call.data.split(':')[1])
    await state.set_state(States.get_limit_set_amount)
    await state.update_data(target_user_id=user_id)
    await safe_edit_message(call, f"Введите, сколько попыток должно <b>ОСТАТЬСЯ</b> у пользователя <code>{user_id}</code> на сегодня:", reply_markup=get_back_keyboard(f"limit_user_menu:{user_id}"))

@dp.message(StateFilter(States.get_limit_set_amount))
async def process_set_limit_amount(message: Message, state: FSMContext):
    try:
        amount = int(message.text)
        if amount < 0: raise ValueError
        user_data = await state.get_data()
        target_user_id = user_data.get('target_user_id')
        new_total = await set_user_sim_attempts(target_user_id, amount)
        await message.reply(f"✅ Успешно! Теперь у пользователя {target_user_id} осталось {new_total} попыток на сегодня.", reply_markup=get_back_keyboard("admin_panel"))
        await state.clear()
    except (ValueError, TypeError): 
        await message.reply("❌ Введите целое неотрицательное число.")
    finally:
        await message.delete()

async def broadcast_worker():
    while True:
        try:
            sent_total = 0
            failed_total = 0
            failed_users = []
            start_time = datetime.now()
            
            task = await broadcast_queue.get()
            
            while True:
                action, chat_id, from_chat_id, message_id, pin_duration = task
                try:
                    if action == 'copy':
                        await bot.copy_message(chat_id=chat_id, from_chat_id=from_chat_id, message_id=message_id)
                    elif action == 'copy_and_pin':
                        sent_message = await bot.copy_message(chat_id=chat_id, from_chat_id=from_chat_id, message_id=message_id)
                        if pin_duration and pin_duration > 0:
                            await bot.pin_chat_message(chat_id, sent_message.message_id, disable_notification=False)
                            asyncio.create_task(unpin_message_after_delay(chat_id, sent_message.message_id, pin_duration))
                    
                    sent_total += 1
                except Exception as e:
                    logging.error(f"Ошибка при отправке сообщения в чат {chat_id}: {e}")
                    failed_total += 1
                    failed_users.append(str(chat_id))
                
                try:
                    task = broadcast_queue.get_nowait()
                    broadcast_queue.task_done()
                except asyncio.QueueEmpty:
                    broadcast_queue.task_done()
                    break

                await asyncio.sleep(0.1)

            end_time = datetime.now()
            duration = (end_time - start_time).total_seconds()
            report_text = (
                f"✅ Рассылка завершена за {duration:.2f} сек.\n\n"
                f"Отправлено: {sent_total}\n"
                f"Не удалось: {failed_total}"
            )
            if failed_users:
                report_text += f"\n\nID с ошибкой: <code>{', '.join(failed_users)}</code>"
            
            await log_system_action(report_text)

        except Exception as e:
            logging.critical(f"Критическая ошибка в воркере рассылки: {e}")

@dp.errors()
async def error_handler(event: ErrorEvent):
    update = event.update
    exception = event.exception

    if isinstance(exception, TelegramBadRequest) and "message to delete not found" in exception.message:
        logging.warning(f"Обработана ошибка 'message to delete not found' для апдейта {update.update_id}.")
        return True

    logging.error(f"Критическая ошибка при обработке апдейта {update.update_id}: {exception}", exc_info=True)
    
    error_text = (
        f"‼️ <b>Произошла критическая ошибка!</b>\n\n"
        f"<b>Тип ошибки:</b> {type(exception).__name__}\n"
        f"<b>Сообщение:</b> {html.quote(str(exception))}\n"
    )
    
    if update.message:
        chat_id = update.message.chat.id
    elif update.callback_query:
        chat_id = update.callback_query.message.chat.id
    else:
        chat_id = None

    if chat_id:
        try:
            await bot.send_message(chat_id, "Произошла непредвиденная ошибка. Мы уже работаем над этим. Попробуйте позже.")
        except Exception as e:
            logging.error(f"Не удалось отправить сообщение об ошибке пользователю в чат {chat_id}: {e}")
            
    await log_system_action(error_text)
    return True

# --- ФУНКЦИИ ЗАПУСКА И ЖИЗНЕННОГО ЦИКЛА ---

async def initialize_bot_data():
    """Инициализирует все данные бота: БД и кэш статистики."""
    logging.info("Инициализация данных бота...")
    await initialize_stats_file()
    await load_database()
    await update_stats_cache()
    logging.info("Данные бота успешно инициализированы.")

async def on_startup(bot: Bot):
    """Действия при запуске бота."""
    # Проверка наличия файлов данных
    if not os.path.exists(DB_FILE) or not os.path.exists(STATS_FILE):
        logging.warning("Файлы данных не найдены. Запуск в режиме восстановления.")
        await request_files_from_admin(ADMIN_IDS)
    else:
        await initialize_bot_data()
        scheduler.add_job(scheduled_files_backup, 'interval', minutes=BACKUP_INTERVAL_MINUTES, id="scheduled_files_backup", replace_existing=True)
    
    scheduler.start()
    logging.info("Планировщик запущен.")

async def on_shutdown(bot: Bot):
    """Действия при остановке бота."""
    logging.warning("Бот останавливается...")
    scheduler.shutdown()
    logging.warning("Планировщик остановлен.")

async def main():
    """Основная функция запуска."""
    log_format = "%(asctime)s -- %(levelname)s: %(message)s"
    date_format = "%d.%m.%Y -- %H:%M:%S"
    logging.basicConfig(level=logging.INFO, format=log_format, datefmt=date_format, handlers=[
        logging.StreamHandler(),
        RotatingFileHandler(LOG_FILE, maxBytes=5*1024*1024, backupCount=2, encoding='utf-8')
    ])
    
    dp.errors.register(error_handler)
    dp.startup.register(on_startup)
    dp.shutdown.register(on_shutdown)
    dp.update.middleware(AuthMiddleware())

    asyncio.create_task(broadcast_worker())

    if LAUNCH_MODE == "webhook":
        # Запуск в режиме вебхука (для Render)
        logging.info(f"Запуск в режиме ВЕБХУКА. URL: {WEBHOOK_URL}")
        await bot.set_webhook(f"{WEBHOOK_URL}/{TOKEN}", drop_pending_updates=True)
        
        app = web.Application()
        webhook_requests_handler = SimpleRequestHandler(dispatcher=dp, bot=bot)
        webhook_requests_handler.register(app, path=f"/{TOKEN}")
        setup_application(app, dp, bot=bot)
        
        runner = web.AppRunner(app)
        await runner.setup()
        # Render предоставляет порт через переменную окружения PORT
        port = int(os.environ.get('PORT', 8000))
        site = web.TCPSite(runner, '0.0.0.0', port)
        await site.start()
        logging.info(f"Веб-сервер запущен на порту {port}")
        await asyncio.Event().wait()
    else:
        # Запуск в режиме поллинга (для ПК)
        logging.info("Запуск в режиме ПОЛЛИНГА.")
        await bot.delete_webhook(drop_pending_updates=True)
        await dp.start_polling(bot)

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logging.info("Бот остановлен вручную.")
