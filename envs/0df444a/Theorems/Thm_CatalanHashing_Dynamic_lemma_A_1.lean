-- Prove2me | Theorems.Thm_CatalanHashing_Dynamic_lemma_A_1
-- name    : CatalanHashing.Dynamic.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:06:11.450314+00:00
-- url     : https://prove2.me/theorems/9c8b0539-1c02-437c-9447-7793dcccf7c2
-- title:
--   Lemma A.1 — correctness of the Catalan parser: it assembles every item lying at or after the start cell; frame and suffix-counter invariants
-- statement:
--   Let a table with $m$ cells, at least one of them empty (load $<1$, the standing assumption under which runs are defined, p. 7), carry a placement with the Catalan nesting property, each cell holding the word of the item placed there and the delimiter tag of the Catalan representation, and run the Catalan parser forward from a cell $t$. Then:
--
--   1. every item $y$ whose interval $I_y=[a_y,b_y]$ lies at or after $t$ ($a_y$ is no later than $b_y$ in the forward scan from $t$, and the scan reaches $b_y$ without meeting an empty cell) is completed at the cell $b_y$ with its words $y_0,\dots,y_{|y|-1}$ in logical order;
--   2. at every step $n$ before the scan meets an empty cell, the stack consists of frames of pairwise distinct items, each of which opened at or after $t$, and each frame holds exactly the words of its item read so far (so $\mathrm{cnt}\le|y|$);
--   3. at every such step, if $f>0$ then $f$ is the number of words read so far of one item $w$ that opened before $t$ ($t\in I_w$, $a_w\neq t$) and has not yet closed, $f\le|w|$, and $w$ is the innermost such item: $I_w\subsetneq I_{w'}$ for every other item $w'$ that opened before $t$ and has not yet closed.
--
--   In symbols, item 1 reads: the parser's output after reading the cells $t,\dots,b_y$ contains $(\mathrm{cdist}(t,b_y),\ [y_0,\dots,y_{|y|-1}])$.
--
--   This is what makes queries that start in the middle of a run well defined: the parser never mixes words of different items.
--
--   Differences from the source:
--
--   - reading: a frame keeps a counter cnt, a match flag and a key buffer (and later the canonical cell and value) → a frame buffers the words of its item read so far; cnt is the buffer length; reason: the match flag, the canonical cell and the value are functions of the buffered words; the lemma is about which words each frame receives
--   - reading: "every item y whose entire interval I_y lies at or after t" → a_y is no later than b_y in the forward order from t, and every cell from t through b_y is occupied; reason: the scan stops at the first empty cell (transition (vii)), so "at or after t" refers to the part of the run that the scan reads
--   - reading: "correctly assembles, in logical word order" → the parser output contains (cdist t b_y, [word 0 of y, ..., word |y|-1 of y]) after reading t, ..., b_y; reason: assembling means completing the item with its words in order; completion happens when its last cell is read
--   - reading: "opened before t", "has not yet closed", "at every step of the scan" → t ∈ I_w and a_w ≠ t; the last cell of w is at forward distance ≥ n from t; every n such that the cells t, ..., t+n-1 are all occupied; reason: literal readings in the cyclic order from t; after an empty cell the scan has stopped
--   - reading: standing assumption load(S) < 1 ("Whenever load(S) < 1, at least one cell of H is empty, so every run is preceded immediately by an empty cell and has a well-defined left-to-right linear order", p. 7) → hypothesis ∃ d, occ d = none; reason: runs and "at or after t" are defined only under it; on a full table (m = 2, one 2-word item, t = 0, n = 3) the scan wraps and clause (1) fails
--   - reading: Definition 3.1: "within every run", for distinct items x and y → CatalanNesting: every interval I_x consists of occupied cells (lies in a run), and clauses (1)-(2) hold for all pairs of distinct items; reason: Definition 3.1 presupposes that each stored item lies in a run; items of different runs have disjoint intervals, so the pairwise clauses add nothing for them
--   - encoding: cells {0, ..., m-1} indexed cyclically, words of x numbered 1..|x| → Fin m with the forward distance cdist, words numbered 0..|x|-1; reason: index base and cyclic arithmetic only
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), p. 40, Lemma A.1 (PDF 41)

import Mathlib
import Definitions.Def_CatalanHashing_Dynamic_Static

namespace CatalanHashing.Dynamic

/-- Lemma A.1 (correctness of the Catalan parser). For a placement with the Catalan nesting
property in a table with at least one empty cell (load `< 1`, so every run is preceded by an
empty cell) and a scan starting at cell `t`: every item whose interval lies at or after `t` (and
is reached before the scan meets an empty cell) is completed, at its last cell, with its words
in logical order; and at every step (1) the stack holds one frame per distinct item that
opened at or after `t`, each holding the words of that item seen so far, and (2) when `f > 0`,
`f` is the number of words seen of one item `w` that opened before `t` and has not closed,
the innermost such item. -/
theorem lemma_A_1 {m : ℕ} {ι W : Type*} (len : ι → ℕ) (hlen : ∀ x, 1 ≤ len x)
    (occ : Occupancy m ι) (hpl : IsPlacement len occ) (hnest : CatalanNesting len occ)
    (hempty : ∃ d, occ d = none)
    (itemWord : ι → ℕ → W) (cellWord : Fin m → W)
    (hword : ∀ d x j, occ d = some (x, j) → cellWord d = itemWord x j) (t : Fin m) :
    (∀ y a e, occ a = some (y, 0) → occ e = some (y, len y - 1) → cdist t a ≤ cdist t e →
      (∀ d ≤ cdist t e, occ (shift t d) ≠ none) →
      (cdist t e, (List.range (len y)).map (itemWord y)) ∈
        (parseRun (tagOf len occ) cellWord t (cdist t e + 1)).2) ∧
    (∀ n, (∀ d < n, occ (shift t d) ≠ none) →
      (∃ ys : List ι, ys.Nodup ∧
        (parseRun (tagOf len occ) cellWord t n).1.stack =
          ys.map (fun y => seenWords occ itemWord t y n) ∧
        ∀ y ∈ ys, (∃ a, occ a = some (y, 0) ∧ cdist t a < n) ∧
          (seenWords occ itemWord t y n).length ≤ len y) ∧
      (0 < (parseRun (tagOf len occ) cellWord t n).1.f →
        ∃ w, (∃ a, occ a = some (w, 0) ∧ a ≠ t ∧ InInterval len occ w t) ∧
          (∃ e, occ e = some (w, len w - 1) ∧ n ≤ cdist t e) ∧
          (parseRun (tagOf len occ) cellWord t n).1.f = (seenWords occ itemWord t w n).length ∧
          (parseRun (tagOf len occ) cellWord t n).1.f ≤ len w ∧
          ∀ w', w' ≠ w → (∃ a, occ a = some (w', 0) ∧ a ≠ t ∧ InInterval len occ w' t) →
            (∃ e, occ e = some (w', len w' - 1) ∧ n ≤ cdist t e) →
            StrictSubInterval len occ w w')) := by sorry

end CatalanHashing.Dynamic
