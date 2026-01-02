"""
FOA_Implementation.py
"""

import tkinter as tk
from tkinter import messagebox, filedialog, simpledialog, ttk
import copy, time, random, threading

# -----------------------------
# Sudoku data model
# -----------------------------
class SudokuBoard:
    def __init__(self, grid=None):
        self.grid = [row[:] for row in grid] if grid else [[0]*9 for _ in range(9)]

    @staticmethod
    def from_string(s):
        s = ''.join(ch for ch in s if ch.isdigit() or ch in '.0')
        if len(s) < 81:
            raise ValueError("Puzzle must contain at least 81 characters (digits/0/.)")
        grid = [[0]*9 for _ in range(9)]
        for i,ch in enumerate(s[:81]):
            r,c = divmod(i,9)
            grid[r][c] = 0 if ch in '.0' else int(ch)
        return SudokuBoard(grid)

    def copy(self):
        return SudokuBoard(self.grid)

    def find_empty(self):
        for r in range(9):
            for c in range(9):
                if self.grid[r][c] == 0:
                    return (r,c)
        return None

    def is_valid_move(self, r, c, val):
        if val == 0: return True
        for j in range(9):
            if j != c and self.grid[r][j] == val:
                return False
        for i in range(9):
            if i != r and self.grid[i][c] == val:
                return False
        br,bc = (r//3)*3, (c//3)*3
        for i in range(br,br+3):
            for j in range(bc,bc+3):
                if (i,j) != (r,c) and self.grid[i][j] == val:
                    return False
        return True

    def is_consistent(self):
        # quick check: no duplicates among filled cells
        for r in range(9):
            seen=set()
            for c in range(9):
                v=self.grid[r][c]
                if v!=0:
                    if v in seen: return False
                    seen.add(v)
        for c in range(9):
            seen=set()
            for r in range(9):
                v=self.grid[r][c]
                if v!=0:
                    if v in seen: return False
                    seen.add(v)
        for br in (0,3,6):
            for bc in (0,3,6):
                seen=set()
                for i in range(br,br+3):
                    for j in range(bc,bc+3):
                        v=self.grid[i][j]
                        if v!=0:
                            if v in seen: return False
                            seen.add(v)
        return True

# -----------------------------
# Backtracking solver
# -----------------------------
class BacktrackingSolver:
    def __init__(self):
        self.nodes = 0
        self.backtracks = 0

    def solve(self, board: SudokuBoard, limit_nodes=None):
        self.nodes = 0
        self.backtracks = 0
        start = time.time()
        ok = self._dfs(board, limit_nodes)
        elapsed = time.time() - start
        return ok, elapsed, self.nodes, self.backtracks

    def _dfs(self, board, limit):
        self.nodes += 1
        if limit and self.nodes > limit:
            return False
        empty = board.find_empty()
        if not empty:
            return True
        r,c = empty
        for v in range(1,10):
            if board.is_valid_move(r,c,v):
                board.grid[r][c] = v
                if self._dfs(board, limit): return True
                board.grid[r][c] = 0
                self.backtracks += 1
        return False

    def count_solutions(self, board: SudokuBoard, limit=2):
        self._count = 0
        def dfs(b):
            if self._count >= limit: return
            e = b.find_empty()
            if not e:
                self._count += 1; return
            r,c = e
            for v in range(1,10):
                if b.is_valid_move(r,c,v):
                    b.grid[r][c]=v
                    dfs(b)
                    b.grid[r][c]=0
                    if self._count >= limit: return
        dfs(board)
        return self._count

# -----------------------------
# CSP solver (AC-3 + MRV + LCV)
# -----------------------------
class CSPSolver:
    def __init__(self):
        self.nodes = 0
        self.backtracks = 0

    def solve(self, board: SudokuBoard):
        domains = {(r,c): set(range(1,10)) if board.grid[r][c]==0 else {board.grid[r][c]}
                   for r in range(9) for c in range(9)}
        if not self.ac3(domains):
            return None, 0, 0, 0
        self.nodes = 0; self.backtracks = 0
        start = time.time()
        res = self._backtrack(domains)
        elapsed = time.time() - start
        if res:
            out = SudokuBoard([[0]*9 for _ in range(9)])
            for (r,c),val in res.items(): out.grid[r][c] = val
            return out, elapsed, self.nodes, self.backtracks
        return None, elapsed, self.nodes, self.backtracks

    def neighbors(self, var):
        r,c = var
        neigh=[]
        for i in range(9):
            if i!=c: neigh.append((r,i))
            if i!=r: neigh.append((i,c))
        br,bc=(r//3)*3,(c//3)*3
        for i in range(br,br+3):
            for j in range(bc,bc+3):
                if (i,j)!=var and (i,j) not in neigh: neigh.append((i,j))
        return neigh

    def ac3(self, domains):
        from collections import deque
        q = deque()
        for xi in domains:
            for xj in self.neighbors(xi): q.append((xi,xj))
        while q:
            xi,xj = q.popleft()
            if self.revise(domains, xi, xj):
                if not domains[xi]: return False
                for xk in self.neighbors(xi):
                    if xk!=xj: q.append((xk, xi))
        return True

    def revise(self, domains, xi, xj):
        removed=False; rem=set()
        for a in set(domains[xi]):
            if not any(self.vals_consistent(xi,a,xj,b) for b in domains[xj]):
                rem.add(a)
        if rem:
            domains[xi] -= rem; removed=True
        return removed

    def vals_consistent(self, xi,a,xj,b):
        (r1,c1),(r2,c2)=xi,xj
        if r1==r2 or c1==c2 or (r1//3==r2//3 and c1//3==c2//3): return a!=b
        return True

    def select_unassigned(self, domains):
        un=[v for v in domains if len(domains[v])>1]
        if not un: return None
        mrv = min(len(domains[v]) for v in un)
        cands=[v for v in un if len(domains[v])==mrv]
        if len(cands)==1: return cands[0]
        best,bd=None,-1
        for v in cands:
            deg = sum(1 for n in self.neighbors(v) if len(domains[n])>1)
            if deg>bd:
                bd=deg; best=v
        return best

    def order_values(self,var,domains):
        costs=[]
        for val in domains[var]:
            cost = sum(1 for n in self.neighbors(var) if val in domains[n])
            costs.append((cost,val))
        costs.sort()
        return [v for _,v in costs]

    def consistent_with_neighbors(self,var,val,domains):
        for n in self.neighbors(var):
            if len(domains[n])==1 and next(iter(domains[n]))==val: return False
        return True

    def _backtrack(self, domains):
        self.nodes += 1
        if all(len(domains[v])==1 for v in domains): return {v: next(iter(domains[v])) for v in domains}
        var = self.select_unassigned(domains)
        if var is None: return None
        for val in self.order_values(var, domains):
            if self.consistent_with_neighbors(var,val,domains):
                new = copy.deepcopy(domains); new[var] = {val}
                if self.ac3(new):
                    res = self._backtrack(new)
                    if res: return res
                self.backtracks += 1
        return None

# -----------------------------
# Puzzle generator
# -----------------------------
class Generator:
    def __init__(self):
        self.bt = BacktrackingSolver()

    def generate_full(self):
        board = SudokuBoard([[0]*9 for _ in range(9)])
        nums = list(range(1,10))
        def fill(idx=0):
            if idx==81: return True
            r,c = divmod(idx,9)
            if board.grid[r][c]!=0: return fill(idx+1)
            random.shuffle(nums)
            for v in nums:
                if board.is_valid_move(r,c,v):
                    board.grid[r][c]=v
                    if fill(idx+1): return True
                    board.grid[r][c]=0
            return False
        for k in (0,3,6):
            vals=list(range(1,10)); random.shuffle(vals); idx=0
            for i in range(k,k+3):
                for j in range(k,k+3):
                    board.grid[i][j]=vals[idx]; idx+=1
        fill(0)
        return board

    def make_puzzle(self, difficulty='Medium'):
        targets={'Easy':36,'Medium':46,'Hard':54}
        target = targets.get(difficulty,46)
        full = self.generate_full()
        positions=[(r,c) for r in range(9) for c in range(9)]
        random.shuffle(positions)
        puzzle = full.copy()
        removed=0
        for (r,c) in positions:
            if removed >= target: break
            backup = puzzle.grid[r][c]; puzzle.grid[r][c]=0
            temp = puzzle.copy()
            count = self.bt.count_solutions(temp, limit=2)
            if count != 1:
                puzzle.grid[r][c]=backup
            else:
                removed += 1
        return puzzle

# -----------------------------
# Main UI
# -----------------------------
class SudokuApp:
    def __init__(self, root):
        self.root = root
        root.title("Sudoku Solver")
        root.resizable(False, False)
        self.bt_solver = BacktrackingSolver()
        self.csp_solver = CSPSolver()
        self.generator = Generator()
        self.history=[]
        self.given = [[False]*9 for _ in range(9)]
        self.conflicts = set()
        self.animate_speed = 60
        self._build_menu()
        self._build_ui()
        self._startup_preference()

    def _build_menu(self):
        menubar = tk.Menu(self.root)
        helpmenu = tk.Menu(menubar, tearoff=0)
        helpmenu.add_command(label="Instructions", command=self.show_instructions)
        helpmenu.add_command(label="About", command=lambda: messagebox.showinfo("About", "Sudoku Solver — FOA PBL"))
        menubar.add_cascade(label="Help", menu=helpmenu)
        self.root.config(menu=menubar)

    def _build_ui(self):
        header = tk.Label(self.root, text="Sudoku Solver", font=("Helvetica",18,"bold"))
        header.pack(pady=(6,4))

        main = tk.Frame(self.root, padx=12, pady=6)
        main.pack()

        grid_frame = tk.Frame(main)
        grid_frame.grid(row=0, column=0, padx=(0,12))

        self.vars = [[tk.StringVar() for _ in range(9)] for _ in range(9)]
        self.entries = [[None]*9 for _ in range(9)]
        font = ("Helvetica", 16)

        for r in range(9):
            for c in range(9):
                vcmd = (self.root.register(self._validate_cell), '%P')
                e = tk.Entry(grid_frame, width=3, font=font, justify='center', textvariable=self.vars[r][c],
                             bg="white", fg="black", bd=2, relief='ridge', validate='key', validatecommand=vcmd)
                e.grid(row=r, column=c, padx=(2 if c%3 else 6), pady=(2 if r%3 else 6))
                e.bind("<KeyRelease>", lambda ev, rr=r, cc=c: self._on_edit(ev, rr, cc))
                self.entries[r][c] = e

        controls = tk.Frame(main)
        controls.grid(row=0, column=1, sticky="n")

        # Generator controls (single dropdown)
        tk.Label(controls, text="Generate puzzle", font=("Helvetica",11,"bold")).pack(anchor="w", pady=(0,4))
        self.gen_combo = ttk.Combobox(controls, values=["Easy","Medium","Hard"], state="readonly", width=17)
        self.gen_combo.set("Medium"); self.gen_combo.pack()
        tk.Button(controls, text="Generate Puzzle", width=20, command=self.generate_selected).pack(pady=4)

        # Upload / Create
        tk.Label(controls, text="Board operations", font=("Helvetica",11,"bold")).pack(anchor="w", pady=(8,4))
        tk.Button(controls, text="Upload puzzle (file)", width=20, command=self.upload_puzzle).pack(pady=2)
        tk.Button(controls, text="Create Empty Board", width=20, command=self.create_empty).pack(pady=2)

        # Solving & hint
        tk.Label(controls, text="Solving options", font=("Helvetica",11,"bold")).pack(anchor="w", pady=(8,4))
        tk.Button(controls, text="Solve (Backtracking)", width=20, command=self.solve_backtracking).pack(pady=3)
        tk.Button(controls, text="Solve (CSP)", width=20, command=self.solve_csp).pack(pady=3)
        tk.Button(controls, text="Animated Solve (CSP)", width=20, command=lambda: threading.Thread(target=self.animated_solve, args=("csp",)).start()).pack(pady=3)
        tk.Button(controls, text="Hint (CSP): reveal one safe cell", width=24, command=self.hint_one).pack(pady=(6,2))

        # Utilities
        tk.Label(controls, text="Utilities", font=("Helvetica",11,"bold")).pack(anchor="w", pady=(8,4))
        tk.Button(controls, text="Validate Board (highlights errors)", width=24, command=self.validate_board).pack(pady=2)
        tk.Button(controls, text="Clear Highlights", width=20, command=self.clear_highlights).pack(pady=2)
        tk.Button(controls, text="Reset (undo all)", width=20, command=self.reset_board).pack(pady=2)
        tk.Button(controls, text="Instructions", width=20, command=self.show_instructions).pack(pady=4)
        tk.Button(controls, text="Exit", width=20, command=self.root.destroy).pack(pady=(6,2))

        # status & stats
        self.status_var = tk.StringVar(); self.status_var.set("Ready")
        self.stats_var = tk.StringVar(); self.stats_var.set("")
        tk.Label(self.root, textvariable=self.status_var, anchor="w").pack(fill="x", padx=8, pady=(6,0))
        tk.Label(self.root, textvariable=self.stats_var, anchor="w", fg="darkblue").pack(fill="x", padx=8)

    # ---------- startup preference (no sample option) ----------
    def _startup_preference(self):
        pref = tk.Toplevel(self.root); pref.transient(self.root); pref.grab_set()
        pref.title("Choose action")
        tk.Label(pref, text="What would you like to do?", font=("Helvetica",12,"bold")).pack(padx=12, pady=(8,6))
        choice = tk.StringVar(value="create")
        tk.Radiobutton(pref, text="Create / Edit board", variable=choice, value="create").pack(anchor="w", padx=12)
        tk.Radiobutton(pref, text="Generate a random puzzle", variable=choice, value="gen").pack(anchor="w", padx=12)
        tk.Radiobutton(pref, text="Upload a puzzle from file", variable=choice, value="upload").pack(anchor="w", padx=12)

        def go():
            sel = choice.get(); pref.destroy()
            if sel=="create":
                self.create_empty()
            elif sel=="gen":
                d = simpledialog.askstring("Generate", "Difficulty: Easy / Medium / Hard", initialvalue="Medium")
                if d and d.capitalize() in ("Easy","Medium","Hard"): self.generate_selected_fixed(d.capitalize())
            elif sel=="upload":
                self.upload_puzzle()
            self.status("Ready")
        tk.Button(pref, text="Continue", command=go).pack(pady=(8,10))
        self.root.wait_window(pref)

    # ---------- helpers ----------
    def _validate_cell(self, proposed):
        if not proposed: return True
        return proposed.isdigit() and len(proposed) <= 1 and '1' <= proposed <= '9'

    def _on_edit(self, ev, r, c):
        s = self.vars[r][c].get()
        if not s:
            if (r,c) in self.conflicts:
                self.conflicts.discard((r,c))
                self.entries[r][c].config(bg="#F2F2F2" if self.given[r][c] else "white")
            return
        if not s[0].isdigit() or s[0]=='0':
            self.vars[r][c].set("")
            return
        self.vars[r][c].set(s[0])
        if (r,c) in self.conflicts:
            self.conflicts.discard((r,c))
            self.entries[r][c].config(bg="#F2F2F2" if self.given[r][c] else "white")
        self.status("Edited cell")

    def board_from_ui(self):
        b = SudokuBoard()
        for r in range(9):
            for c in range(9):
                s = self.vars[r][c].get().strip()
                b.grid[r][c] = int(s[0]) if s and s[0].isdigit() else 0
        return b

    def set_ui_board(self, board: SudokuBoard, mark_given=True):
        for r in range(9):
            for c in range(9):
                v = board.grid[r][c]
                if v != 0 and mark_given:
                    self.vars[r][c].set(str(v))
                    self.entries[r][c].config(state='readonly', readonlybackground="#F2F2F2", fg="black")
                    self.given[r][c] = True
                else:
                    self.vars[r][c].set("" if v==0 else str(v))
                    self.entries[r][c].config(state='normal', bg="white", fg="black")
                    self.given[r][c] = False
        self.clear_highlights()
        self.stats_var.set("")

    def push_history(self):
        state = [[self.vars[r][c].get() for c in range(9)] for r in range(9)]
        self.history.append(state)
        if len(self.history) > 40: self.history.pop(0)

    def reset_board(self):
        if not self.history:
            self.status("No saved state to reset")
            return
        first = self.history[0]
        for r in range(9):
            for c in range(9):
                self.vars[r][c].set(first[r][c])
                self.entries[r][c].config(state='normal', bg="white")
                self.given[r][c] = False
        self.history.clear()
        self.clear_highlights()
        self.status("Reset to first saved state")

    def status(self, text):
        self.status_var.set(text)

    def show_stats(self, elapsed, nodes, backtracks):
        self.stats_var.set(f"Time: {elapsed:.4f}s    Nodes: {nodes}    Backtracks: {backtracks}")

    # ---------- generate/upload/create ----------
    def generate_selected(self):
        diff = self.gen_combo.get()
        if diff not in ("Easy","Medium","Hard"): diff="Medium"
        self.generate_selected_fixed(diff)

    def generate_selected_fixed(self, difficulty):
        ok = messagebox.askyesno("Generate", f"Generate a {difficulty} puzzle? This may take a few seconds.")
        if not ok: return
        self.push_history(); self.status("Generating puzzle...")
        def worker():
            p = self.generator.make_puzzle(difficulty)
            self.root.after(0, lambda: self.set_ui_board(p, mark_given=True))
            self.root.after(0, lambda: self.status(f"Generated {difficulty} puzzle"))
        threading.Thread(target=worker).start()

    def upload_puzzle(self):
        path = filedialog.askopenfilename(title="Open puzzle file", filetypes=[("Text files","*.txt"),("All files","*.*")])
        if not path: return
        try:
            with open(path,'r') as f: raw = f.read()
            b = SudokuBoard.from_string(raw)
            self.push_history(); self.set_ui_board(b, mark_given=True); self.status("Loaded puzzle from file")
        except Exception as e:
            messagebox.showerror("Upload error", str(e))

    def create_empty(self):
        self.push_history()
        for r in range(9):
            for c in range(9):
                self.vars[r][c].set("")
                self.entries[r][c].config(state='normal', bg="white")
                self.given[r][c] = False
        self.clear_highlights()
        self.status("Empty board created — you can edit cells")

    # ---------- validate / highlights ----------
    def validate_board(self):
        b = self.board_from_ui()
        conflicts = set()
        # rows
        for r in range(9):
            seen = {}
            for c in range(9):
                v = b.grid[r][c]
                if v==0: continue
                if v in seen:
                    conflicts.add((r,c)); conflicts.add((r,seen[v]))
                else:
                    seen[v]=c
        # cols
        for c in range(9):
            seen = {}
            for r in range(9):
                v = b.grid[r][c]
                if v==0: continue
                if v in seen:
                    conflicts.add((r,c)); conflicts.add((seen[v],c))
                else:
                    seen[v]=r
        # boxes
        for br in (0,3,6):
            for bc in (0,3,6):
                seen = {}
                for i in range(br,br+3):
                    for j in range(bc,bc+3):
                        v = b.grid[i][j]
                        if v==0: continue
                        if v in seen:
                            conflicts.add((i,j)); conflicts.add(seen[v])
                        else:
                            seen[v]=(i,j)
        self.conflicts = conflicts
        if not conflicts:
            self.status("Board valid: no immediate conflicts.")
            for r in range(9):
                for c in range(9):
                    self.entries[r][c].config(bg="#F2F2F2" if self.given[r][c] else "white")
        else:
            self.status(f"Board has {len(conflicts)} conflicting cells (highlighted in red).")
            for r in range(9):
                for c in range(9):
                    if (r,c) in conflicts:
                        self.entries[r][c].config(bg="#FFB8B8")
                    else:
                        self.entries[r][c].config(bg="#F2F2F2" if self.given[r][c] else "white")

    def clear_highlights(self):
        self.conflicts.clear()
        for r in range(9):
            for c in range(9):
                self.entries[r][c].config(bg="#F2F2F2" if self.given[r][c] else "white")
        self.status("Highlights cleared")

    # ---------- hint (single cell) ----------
    def hint_one(self):
        b = self.board_from_ui()
        if not b.is_consistent():
            if not messagebox.askyesno("Warning","Board has conflicts. Hint may be misleading. Continue?"): return
        self.status("Computing hint (CSP)...")
        def worker():
            solved, elapsed, nodes, back = self.csp_solver.solve(b)
            if not solved:
                self.root.after(0, lambda: self.status("No hint: puzzle invalid or unsolvable."))
                return
            for r in range(9):
                for c in range(9):
                    if b.grid[r][c] == 0:
                        val = solved.grid[r][c]
                        def apply_hint(rr=r, cc=c, vv=val, el=elapsed, nd=nodes, bk=back):
                            self.push_history()
                            self.vars[rr][cc].set(str(vv))
                            self.entries[rr][cc].config(bg="#DFF7DF")
                            self.show_stats(el, nd, bk)
                            self.status(f"Hint applied at ({rr+1},{cc+1}) = {vv}")
                            self.root.after(1200, lambda: self.entries[rr][cc].config(bg="#F2F2F2" if self.given[rr][cc] else "white"))
                        self.root.after(0, apply_hint)
                        return
            self.root.after(0, lambda: self.status("Board complete — no hint available"))
        threading.Thread(target=worker).start()

    # ---------- solvers ----------
    def solve_backtracking(self):
        b = self.board_from_ui()
        if not b.is_consistent() and not messagebox.askyesno("Warning","Conflicts present. Try solve anyway?"): return
        self.push_history(); self.status("Solving with Backtracking...")
        def worker():
            ok, elapsed, nodes, back = self.bt_solver.solve(b)
            if ok:
                self.root.after(0, lambda: self.set_ui_board(b, mark_given=False))
                self.root.after(0, lambda: self.show_stats(elapsed,nodes,back))
                self.root.after(0, lambda: self.status("Solved with Backtracking"))
            else:
                self.root.after(0, lambda: self.status("Backtracking failed or timed out"))
        threading.Thread(target=worker).start()

    def solve_csp(self):
        b = self.board_from_ui()
        if not b.is_consistent() and not messagebox.askyesno("Warning","Conflicts present. Try solve anyway?"): return
        self.push_history(); self.status("Solving with CSP...")
        def worker():
            solved, elapsed, nodes, back = self.csp_solver.solve(b)
            if solved:
                self.root.after(0, lambda: self.set_ui_board(solved, mark_given=False))
                self.root.after(0, lambda: self.show_stats(elapsed,nodes,back))
                self.root.after(0, lambda: self.status("Solved with CSP"))
            else:
                self.root.after(0, lambda: self.status("CSP could not find a solution"))
        threading.Thread(target=worker).start()

    def animated_solve(self, method="csp"):
        b = self.board_from_ui()
        self.push_history(); self.status("Preparing animation...")
        if method=="csp":
            solved, elapsed, nodes, back = self.csp_solver.solve(b)
        else:
            ok, elapsed, nodes, back = self.bt_solver.solve(b); solved = b if ok else None
        if not solved:
            self.status("No solution for animation")
            return
        cells = [(r,c, solved.grid[r][c]) for r in range(9) for c in range(9) if b.grid[r][c]==0]
        if not cells:
            self.status("Nothing to animate (board complete)")
            return
        self.status("Animating solution...")
        for r,c,val in cells:
            time.sleep(self.animate_speed/1000.0)
            self.root.after(0, lambda rr=r,cc=c,vv=val: self.vars[rr][cc].set(str(vv)))
        self.root.after(0, lambda: self.show_stats(elapsed,nodes,back))
        self.root.after(0, lambda: self.status("Animation complete"))

    # ---------- instructions/help ----------
    def show_instructions(self):
        instructions = (
            "Sudoku rules (short):\n"
            "- Fill every row, column and 3×3 box with digits 1–9 exactly once.\n\n"
            "How to use this app:\n"
            "1) Generate: choose difficulty and press Generate to get a puzzle (unique solution).\n"
            "2) Upload: load an 81-character puzzle file (use 0 or . for blanks).\n"
            "3) Create Empty Board: start typing your own puzzle.\n"
            "4) Clues (from Generate/Upload) are readonly so you won't change given numbers by mistake.\n"
            "5) Validate Board: highlights conflicting cells in red (persistent until you clear or fix them).\n"
            "6) Hint (CSP): reveals one safe cell (green) — a small hint only.\n"
            "7) Solve (Backtracking/CSP): compute full solution; use Animated Solve to watch filling.\n\n"
            "Tips:\n- Validate before solving if you're unsure of your entries.\n- Use Reset to revert to the very first saved state.\n"
        )
        messagebox.showinfo("Instructions", instructions)

# -----------------------------
# Run
# -----------------------------
if __name__ == "__main__":
    root = tk.Tk()
    app = SudokuApp(root)
    root.mainloop()