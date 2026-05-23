from __future__ import annotations

import csv
import heapq
import json
import math
import os
import re
import sqlite3
from dataclasses import dataclass
from datetime import datetime
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog


Point = Tuple[int, int]
Grid = List[List[int]]


@dataclass(frozen=True)
class Terrain:
    code: int
    name: str
    cost: float
    color: str
    is_obstacle: bool = False


TERRAINS: Dict[int, Terrain] = {
    0: Terrain(0, "Обычная клетка", 1.0, "#ffffff"),
    1: Terrain(1, "Препятствие", math.inf, "#222222", True),
    2: Terrain(2, "Трава", 1.3, "#b7e4a8"),
    3: Terrain(3, "Песок", 1.8, "#f4d35e"),
    4: Terrain(4, "Вода/сложная поверхность", 2.4, "#8ecae6"),
}

# 4 ортогональных шага, 4 диагональных шага, 8 нестандартных шагов длиной sqrt(5)
MOVES: Sequence[Tuple[int, int, float]] = [
    (-1, 0, 1.0),
    (1, 0, 1.0),
    (0, -1, 1.0),
    (0, 1, 1.0),
    (-1, -1, math.sqrt(2)),
    (-1, 1, math.sqrt(2)),
    (1, -1, math.sqrt(2)),
    (1, 1, math.sqrt(2)),
    (-2, -1, math.sqrt(5)),
    (-2, 1, math.sqrt(5)),
    (2, -1, math.sqrt(5)),
    (2, 1, math.sqrt(5)),
    (-1, -2, math.sqrt(5)),
    (-1, 2, math.sqrt(5)),
    (1, -2, math.sqrt(5)),
    (1, 2, math.sqrt(5)),
]

DEFAULT_GRID: Grid = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 2, 2, 2, 0, 1, 1, 1, 0, 3, 3, 3, 0, 0],
    [0, 2, 1, 2, 0, 0, 0, 1, 0, 3, 1, 3, 0, 0],
    [0, 2, 1, 2, 2, 2, 0, 1, 0, 3, 1, 3, 0, 0],
    [0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 1, 2, 2, 2, 2, 0, 1, 0, 4, 4],
    [0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 1, 0, 4, 4],
    [0, 0, 1, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 1, 0, 3, 0, 2, 2, 2, 2, 0, 0],
    [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2, 0, 0],
]


def is_inside(grid: Grid, point: Point) -> bool:
    r, c = point
    return 0 <= r < len(grid) and 0 <= c < len(grid[0])


def terrain_for(code: int) -> Terrain:
    return TERRAINS.get(code, TERRAINS[0])


def is_passable(grid: Grid, point: Point) -> bool:
    if not is_inside(grid, point):
        return False
    return not terrain_for(grid[point[0]][point[1]]).is_obstacle


def validate_grid(grid: Grid) -> None:
    if not grid or not grid[0]:
        raise ValueError("Сетка пустая.")
    width = len(grid[0])
    for i, row in enumerate(grid):
        if len(row) != width:
            raise ValueError(f"Строка {i + 1} имеет длину {len(row)}, ожидалось {width}.")
        for cell in row:
            if cell not in TERRAINS:
                raise ValueError(f"Неизвестный тип клетки: {cell}. Допустимы: {sorted(TERRAINS)}")


def parse_grid_from_csv(path: str) -> Grid:
    """Читает сетку из CSV/TXT. Разделители: запятая, точка с запятой или пробел."""
    grid: Grid = []
    with open(path, "r", encoding="utf-8-sig") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = [p for p in re.split(r"[;,\s]+", line) if p != ""]
            grid.append([int(p) for p in parts])
    validate_grid(grid)
    return grid


def save_grid_to_csv(grid: Grid, path: str) -> None:
    with open(path, "w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f, delimiter=";")
        writer.writerows(grid)

def bresenham_cells(start: Point, end: Point) -> List[Point]:
    """Возвращает клетки, через которые проходит отрезок от start до end, включая end."""
    r1, c1 = start
    r2, c2 = end
    dr = abs(r2 - r1)
    dc = abs(c2 - c1)
    sr = 1 if r2 >= r1 else -1
    sc = 1 if c2 >= c1 else -1

    cells: List[Point] = []
    r, c = r1, c1

    if dc > dr:
        err = dc / 2
        while c != c2:
            c += sc
            err -= dr
            if err < 0:
                r += sr
                err += dc
            cells.append((r, c))
    else:
        err = dr / 2
        while r != r2:
            r += sr
            err -= dc
            if err < 0:
                c += sc
                err += dr
            cells.append((r, c))

    return cells


def can_move(grid: Grid, start: Point, end: Point) -> bool:
    """Проверяет, можно ли выполнить шаг без перепрыгивания препятствий."""
    if not is_passable(grid, end):
        return False

    sr, sc = start
    er, ec = end
    dr = er - sr
    dc = ec - sc

    # Запрет срезания угла при диагональном ходе.
    if abs(dr) == 1 and abs(dc) == 1:
        if not is_passable(grid, (sr + dr, sc)) or not is_passable(grid, (sr, sc + dc)):
            return False

    # Для нестандартных ходов sqrt(5) проверяем клетки, через которые проходит отрезок.
    # Так алгоритм не может "перепрыгнуть" через стену.
    if abs(dr) + abs(dc) == 3:
        for cell in bresenham_cells(start, end):
            if not is_passable(grid, cell):
                return False

    return True

def get_neighbors(grid: Grid, point: Point) -> Iterable[Tuple[Point, float]]:
    r, c = point
    for dr, dc, base_length in MOVES:
        nxt = (r + dr, c + dc)
        if not is_inside(grid, nxt):
            continue
        if not can_move(grid, point, nxt):
            continue
        terrain_cost = terrain_for(grid[nxt[0]][nxt[1]]).cost
        yield nxt, base_length * terrain_cost


def find_shortest_path(grid: Grid, start: Point, goal: Point) -> Tuple[List[Point], float, Dict[Point, float]]:
    """
    Обобщённый волновой алгоритм Ли для взвешенной сетки.
    Так как стоимость ходов разная, используется очередь с приоритетом, то есть вариант Дейкстры.
    """
    validate_grid(grid)

    if not is_passable(grid, start):
        raise ValueError("Начальная клетка находится на препятствии.")
    if not is_passable(grid, goal):
        raise ValueError("Целевая клетка находится на препятствии.")
    if start == goal:
        return [start], 0.0, {start: 0.0}

    distances: Dict[Point, float] = {start: 0.0}
    previous: Dict[Point, Point] = {}
    queue: List[Tuple[float, Point]] = [(0.0, start)]
    visited = set()

    while queue:
        current_distance, current = heapq.heappop(queue)
        if current in visited:
            continue
        visited.add(current)

        if current == goal:
            break

        for neighbor, step_cost in get_neighbors(grid, current):
            new_distance = current_distance + step_cost
            if new_distance < distances.get(neighbor, math.inf):
                distances[neighbor] = new_distance
                previous[neighbor] = current
                heapq.heappush(queue, (new_distance, neighbor))

    if goal not in distances:
        return [], math.inf, distances

    path = [goal]
    while path[-1] != start:
        path.append(previous[path[-1]])
    path.reverse()
    return path, distances[goal], distances

class GridDatabase:
    def __init__(self, path: str = "lee_grid.db") -> None:
        self.path = path
        self.conn = sqlite3.connect(path)
        self.conn.execute("PRAGMA foreign_keys = ON")
        self.create_tables()
        self.seed_terrains()

    def create_tables(self) -> None:
        cur = self.conn.cursor()
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS terrain_types (
                code INTEGER PRIMARY KEY,
                name TEXT NOT NULL,
                cost REAL NOT NULL,
                is_obstacle INTEGER NOT NULL
            )
            """
        )
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS grids (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                rows_count INTEGER NOT NULL,
                cols_count INTEGER NOT NULL,
                created_at TEXT NOT NULL
            )
            """
        )
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS cells (
                grid_id INTEGER NOT NULL,
                row_index INTEGER NOT NULL,
                col_index INTEGER NOT NULL,
                terrain_code INTEGER NOT NULL,
                PRIMARY KEY (grid_id, row_index, col_index),
                FOREIGN KEY (grid_id) REFERENCES grids(id) ON DELETE CASCADE,
                FOREIGN KEY (terrain_code) REFERENCES terrain_types(code)
            )
            """
        )
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS paths (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                grid_id INTEGER NOT NULL,
                start_row INTEGER NOT NULL,
                start_col INTEGER NOT NULL,
                goal_row INTEGER NOT NULL,
                goal_col INTEGER NOT NULL,
                total_cost REAL NOT NULL,
                steps_count INTEGER NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY (grid_id) REFERENCES grids(id) ON DELETE CASCADE
            )
            """
        )
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS path_cells (
                path_id INTEGER NOT NULL,
                order_no INTEGER NOT NULL,
                row_index INTEGER NOT NULL,
                col_index INTEGER NOT NULL,
                PRIMARY KEY (path_id, order_no),
                FOREIGN KEY (path_id) REFERENCES paths(id) ON DELETE CASCADE
            )
            """
        )
        self.conn.commit()

    def seed_terrains(self) -> None:
        self.conn.executemany(
            """
            INSERT OR REPLACE INTO terrain_types(code, name, cost, is_obstacle)
            VALUES (?, ?, ?, ?)
            """,
            [
                (t.code, t.name, 999999.0 if math.isinf(t.cost) else t.cost, int(t.is_obstacle))
                for t in TERRAINS.values()
            ],
        )
        self.conn.commit()

    def save_grid(self, grid: Grid, name: str) -> int:
        validate_grid(grid)
        cur = self.conn.cursor()
        cur.execute(
            """
            INSERT INTO grids(name, rows_count, cols_count, created_at)
            VALUES (?, ?, ?, ?)
            """,
            (name, len(grid), len(grid[0]), datetime.now().isoformat(timespec="seconds")),
        )
        grid_id = cur.lastrowid
        rows = [
            (grid_id, r, c, grid[r][c])
            for r in range(len(grid))
            for c in range(len(grid[0]))
        ]
        cur.executemany(
            """
            INSERT INTO cells(grid_id, row_index, col_index, terrain_code)
            VALUES (?, ?, ?, ?)
            """,
            rows,
        )
        self.conn.commit()
        return int(grid_id)

    def load_grid(self, grid_id: int) -> Grid:
        cur = self.conn.cursor()
        meta = cur.execute(
            "SELECT rows_count, cols_count FROM grids WHERE id = ?", (grid_id,)
        ).fetchone()
        if meta is None:
            raise ValueError(f"Сетка с id={grid_id} не найдена.")
        rows_count, cols_count = meta
        grid = [[0 for _ in range(cols_count)] for _ in range(rows_count)]
        rows = cur.execute(
            """
            SELECT row_index, col_index, terrain_code
            FROM cells
            WHERE grid_id = ?
            ORDER BY row_index, col_index
            """,
            (grid_id,),
        ).fetchall()
        for r, c, code in rows:
            grid[r][c] = code
        validate_grid(grid)
        return grid

    def get_latest_grid_id(self) -> Optional[int]:
        row = self.conn.execute("SELECT id FROM grids ORDER BY id DESC LIMIT 1").fetchone()
        return int(row[0]) if row else None

    def save_path(self, grid_id: int, start: Point, goal: Point, path: List[Point], total_cost: float) -> int:
        cur = self.conn.cursor()
        cur.execute(
            """
            INSERT INTO paths(grid_id, start_row, start_col, goal_row, goal_col,
                              total_cost, steps_count, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                grid_id,
                start[0],
                start[1],
                goal[0],
                goal[1],
                float(total_cost),
                max(0, len(path) - 1),
                datetime.now().isoformat(timespec="seconds"),
            ),
        )
        path_id = int(cur.lastrowid)
        cur.executemany(
            """
            INSERT INTO path_cells(path_id, order_no, row_index, col_index)
            VALUES (?, ?, ?, ?)
            """,
            [(path_id, i, r, c) for i, (r, c) in enumerate(path)],
        )
        self.conn.commit()
        return path_id

    def close(self) -> None:
        self.conn.close()

class LeeApp:
    def __init__(self) -> None:
        self.root = tk.Tk()
        self.root.title("Волновой алгоритм Ли: поиск кратчайшего пути")
        self.root.geometry("1120x760")

        self.grid: Grid = [row[:] for row in DEFAULT_GRID]
        self.start: Point = (0, 0)
        self.goal: Point = (len(self.grid) - 1, len(self.grid[0]) - 1)
        self.path: List[Point] = []
        self.distances: Dict[Point, float] = {}
        self.mode = "start"
        self.current_grid_id: Optional[int] = None
        self.db = GridDatabase(os.path.join(os.getcwd(), "lee_grid.db"))

        self.cell_size = 34
        self._build_ui()
        self.draw_grid()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def _build_ui(self) -> None:
        main_frame = tk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        left_panel = tk.Frame(main_frame)
        left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))

        title = tk.Label(left_panel, text="Управление", font=("Arial", 14, "bold"))
        title.pack(anchor="w", pady=(0, 8))

        buttons = [
            ("Загрузить CSV", self.load_csv),
            ("Сохранить сетку в SQL", self.save_grid_to_db),
            ("Загрузить последнюю из SQL", self.load_grid_from_db),
            ("Выбрать старт", lambda: self.set_mode("start")),
            ("Выбрать цель", lambda: self.set_mode("goal")),
            ("Запустить алгоритм", self.run_algorithm),
            ("Очистить путь", self.clear_path),
            ("Экспорт текущей сетки", self.export_grid),
            ("Справка", self.show_help),
        ]
        for text, command in buttons:
            tk.Button(left_panel, text=text, command=command, width=26).pack(anchor="w", pady=2)

        self.status = tk.StringVar()
        self.status.set("Кликните по клетке, чтобы выбрать старт.")
        tk.Label(left_panel, textvariable=self.status, wraplength=250, justify=tk.LEFT).pack(
            anchor="w", pady=12
        )

        legend = tk.LabelFrame(left_panel, text="Легенда")
        legend.pack(anchor="w", fill=tk.X, pady=8)
        for terrain in TERRAINS.values():
            row = tk.Frame(legend)
            row.pack(anchor="w", pady=1)
            sample = tk.Label(row, width=3, bg=terrain.color, relief=tk.SOLID, borderwidth=1)
            sample.pack(side=tk.LEFT, padx=4)
            text = f"{terrain.code} — {terrain.name}"
            if not terrain.is_obstacle:
                text += f"; цена {terrain.cost}"
            tk.Label(row, text=text, anchor="w").pack(side=tk.LEFT)

        text = (
            "Формат CSV: числа 0–4 через ;, запятую или пробел.\n"
            "0 — обычная клетка, 1 — препятствие, 2–4 — разные поверхности."
        )
        tk.Label(left_panel, text=text, wraplength=260, justify=tk.LEFT, fg="#444444").pack(
            anchor="w", pady=8
        )

        canvas_frame = tk.Frame(main_frame)
        canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(canvas_frame, bg="#f5f5f5")
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.canvas.bind("<Button-1>", self.on_canvas_click)

        y_scroll = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        y_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        x_scroll = tk.Scrollbar(self.root, orient=tk.HORIZONTAL, command=self.canvas.xview)
        x_scroll.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas.configure(yscrollcommand=y_scroll.set, xscrollcommand=x_scroll.set)

    def set_mode(self, mode: str) -> None:
        self.mode = mode
        if mode == "start":
            self.status.set("Режим: выбор начальной клетки. Кликните по проходимой клетке.")
        else:
            self.status.set("Режим: выбор целевой клетки. Кликните по проходимой клетке.")

    def draw_grid(self) -> None:
        self.canvas.delete("all")
        rows, cols = len(self.grid), len(self.grid[0])
        width, height = cols * self.cell_size, rows * self.cell_size
        self.canvas.configure(scrollregion=(0, 0, width, height))

        path_set = set(self.path)

        for r in range(rows):
            for c in range(cols):
                x1, y1 = c * self.cell_size, r * self.cell_size
                x2, y2 = x1 + self.cell_size, y1 + self.cell_size
                terrain = terrain_for(self.grid[r][c])
                fill = terrain.color
                if (r, c) in path_set:
                    fill = "#ff6b6b"
                if (r, c) == self.start:
                    fill = "#2a9d8f"
                if (r, c) == self.goal:
                    fill = "#4361ee"

                self.canvas.create_rectangle(x1, y1, x2, y2, fill=fill, outline="#cccccc")

                label = "S" if (r, c) == self.start else "G" if (r, c) == self.goal else str(self.grid[r][c])
                text_color = "#ffffff" if terrain.is_obstacle or (r, c) in [self.start, self.goal] else "#222222"
                self.canvas.create_text(
                    x1 + self.cell_size / 2,
                    y1 + self.cell_size / 2,
                    text=label,
                    fill=text_color,
                    font=("Arial", 10, "bold"),
                )

    def on_canvas_click(self, event: tk.Event) -> None:
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        r = int(y // self.cell_size)
        c = int(x // self.cell_size)
        point = (r, c)
        if not is_inside(self.grid, point):
            return
        if not is_passable(self.grid, point):
            messagebox.showwarning("Нельзя выбрать клетку", "Эта клетка является препятствием.")
            return
        if self.mode == "start":
            self.start = point
            self.status.set(f"Старт выбран: {self.start}. Теперь можно выбрать цель.")
        else:
            self.goal = point
            self.status.set(f"Цель выбрана: {self.goal}. Теперь можно запустить алгоритм.")
        self.path = []
        self.draw_grid()

    def load_csv(self) -> None:
        path = filedialog.askopenfilename(
            title="Выберите CSV/TXT файл с сеткой",
            filetypes=[("CSV/TXT", "*.csv *.txt"), ("Все файлы", "*.*")],
        )
        if not path:
            return
        try:
            self.grid = parse_grid_from_csv(path)
            self.start = self.find_first_passable(default=(0, 0))
            self.goal = self.find_last_passable(default=self.start)
            self.path = []
            self.current_grid_id = None
            self.status.set(f"Сетка загружена: {os.path.basename(path)}")
            self.draw_grid()
        except Exception as exc:
            messagebox.showerror("Ошибка загрузки", str(exc))

    def save_grid_to_db(self) -> None:
        name = simpledialog.askstring("Название сетки", "Введите название сетки:", initialvalue="grid")
        if not name:
            return
        try:
            self.current_grid_id = self.db.save_grid(self.grid, name)
            self.status.set(f"Сетка сохранена в SQL. grid_id={self.current_grid_id}")
            messagebox.showinfo("Готово", f"Сетка сохранена в SQLite: grid_id={self.current_grid_id}")
        except Exception as exc:
            messagebox.showerror("Ошибка сохранения", str(exc))

    def load_grid_from_db(self) -> None:
        try:
            grid_id = self.db.get_latest_grid_id()
            if grid_id is None:
                messagebox.showwarning("Нет данных", "В базе пока нет сохранённых сеток.")
                return
            self.grid = self.db.load_grid(grid_id)
            self.current_grid_id = grid_id
            self.start = self.find_first_passable(default=(0, 0))
            self.goal = self.find_last_passable(default=self.start)
            self.path = []
            self.status.set(f"Загружена последняя сетка из SQL: grid_id={grid_id}")
            self.draw_grid()
        except Exception as exc:
            messagebox.showerror("Ошибка загрузки из SQL", str(exc))

    def run_algorithm(self) -> None:
        try:
            path, total_cost, distances = find_shortest_path(self.grid, self.start, self.goal)
            self.path = path
            self.distances = distances
            self.draw_grid()
            if not path:
                self.status.set("Путь не найден. Цель недостижима.")
                messagebox.showwarning("Путь не найден", "Между стартом и целью нет допустимого пути.")
                return

            if self.current_grid_id is None:
                self.current_grid_id = self.db.save_grid(self.grid, "auto_saved_grid")
            path_id = self.db.save_path(self.current_grid_id, self.start, self.goal, path, total_cost)
            msg = (
                f"Путь найден.\n"
                f"Количество шагов: {len(path) - 1}\n"
                f"Стоимость пути: {total_cost:.3f}\n"
                f"path_id в SQL: {path_id}"
            )
            self.status.set(msg)
            messagebox.showinfo("Результат", msg)
        except Exception as exc:
            messagebox.showerror("Ошибка алгоритма", str(exc))

    def clear_path(self) -> None:
        self.path = []
        self.status.set("Путь очищен.")
        self.draw_grid()

    def export_grid(self) -> None:
        path = filedialog.asksaveasfilename(
            title="Сохранить сетку",
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv"), ("Все файлы", "*.*")],
        )
        if not path:
            return
        try:
            save_grid_to_csv(self.grid, path)
            self.status.set(f"Сетка экспортирована: {path}")
        except Exception as exc:
            messagebox.showerror("Ошибка экспорта", str(exc))

    def show_help(self) -> None:
        text = (
            "Программа реализует обобщённый волновой алгоритм Ли.\n\n"
            "Так как ходы имеют разные веса: 1, sqrt(2), sqrt(5), "
            "поиск выполняется через очередь с приоритетом, то есть как алгоритм Дейкстры.\n\n"
            "Правила:\n"
            "1) чёрные клетки — препятствия;\n"
            "2) диагональный ход запрещён, если он срезает угол препятствия;\n"
            "3) ход sqrt(5) запрещён, если на линии движения есть препятствие;\n"
            "4) разные поверхности увеличивают стоимость прохода."
        )
        messagebox.showinfo("Справка", text)

    def find_first_passable(self, default: Point) -> Point:
        for r, row in enumerate(self.grid):
            for c, _ in enumerate(row):
                if is_passable(self.grid, (r, c)):
                    return (r, c)
        return default

    def find_last_passable(self, default: Point) -> Point:
        for r in range(len(self.grid) - 1, -1, -1):
            for c in range(len(self.grid[0]) - 1, -1, -1):
                if is_passable(self.grid, (r, c)):
                    return (r, c)
        return default

    def on_close(self) -> None:
        self.db.close()
        self.root.destroy()

    def run(self) -> None:
        self.root.mainloop()


def path_to_json(path: List[Point], total_cost: float) -> str:
    return json.dumps(
        {
            "total_cost": total_cost,
            "steps_count": max(0, len(path) - 1),
            "path": [{"row": r, "col": c} for r, c in path],
        },
        ensure_ascii=False,
        indent=2,
    )


if __name__ == "__main__":
    app = LeeApp()
    app.run()
