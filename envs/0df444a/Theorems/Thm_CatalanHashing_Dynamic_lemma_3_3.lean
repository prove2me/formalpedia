-- Prove2me | Theorems.Thm_CatalanHashing_Dynamic_lemma_3_3
-- name    : CatalanHashing.Dynamic.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:06:10.494865+00:00
-- url     : https://prove2.me/theorems/6e70dbfc-fe6f-4dba-9143-08aacb1df5de
-- title:
--   Lemma 3.3 — a placement determined by a priority rule satisfies the Catalan nesting property
-- statement:
--   Let a table have $m$ cells and store a finite set of items, item $x$ having length $|x|\ge1$ and an arbitrary canonical cell $c(x)$, with total length $\sum_x|x|<m$ (load below 1). Fix a priority rule, that is, a strict order of the items, and let $H$ be the **bottom-up placement**: in decreasing priority, each item $x$ takes the first $|x|$ empty cells at or after $c(x)$. Then $H$ is a placement and satisfies the **Catalan nesting property**: every interval $I_x$ lies in a run, and for distinct $x,y$
--   $$I_x\cap I_y=\emptyset\ \text{ or }\ I_y\subsetneq I_x\ \text{ or }\ I_x\subsetneq I_y,\qquad I_y\subsetneq I_x\ \Rightarrow\ \text{no cell of } I_y \text{ holds a word of } x.$$
--   This is the structural fact behind every static construction of the paper: whatever the priorities, the delimiter tags of a run form a balanced parenthesis string, so a single forward scan can be parsed.
--
--   Differences from the source:
--
--   - reading: a placement determined by a priority rule → bottomUp len c order for any duplicate-free list order containing every item (the decreasing priority order); reason: a priority rule assigns distinct priorities, i.e. a strict total order; Lemma 3.3 is proved for the bottom-up construction, which the paper shows equivalent to the others
--   - reading: "the placement of items in H" → the conclusion also states IsPlacement (every word stored once, in logical order); reason: Definition 3.1 is a property of placements; the bottom-up output being one is presupposed
--   - reading: standing assumption load(S) < 1 (p. 7; p. 11 "Because the load of S is less than 1") → ∑ x, len x < m and len x ≥ 1; reason: the section-wide assumption of the static constructions; items have |x| ≥ 1 (p. 7)
--   - reading: Definition 3.1: "within every run", for distinct items x and y → CatalanNesting: every interval I_x consists of occupied cells (lies in a run), and clauses (1)-(2) hold for all pairs of distinct items; reason: Definition 3.1 presupposes that each stored item lies in a run; items of different runs have disjoint intervals, so the pairwise clauses add nothing for them
--   - encoding: cells {0, ..., m-1} indexed cyclically, words of x numbered 1..|x| → Fin m with the forward distance cdist, words numbered 0..|x|-1; reason: index base and cyclic arithmetic only
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), p. 11, Lemma 3.3 (PDF 12)

import Mathlib
import Definitions.Def_CatalanHashing_Dynamic_Static

namespace CatalanHashing.Dynamic

/-- Lemma 3.3: a placement determined by a priority rule (the bottom-up construction in the
rule's decreasing priority order) satisfies the Catalan nesting property. -/
theorem lemma_3_3 {m : ℕ} {ι : Type*} [Fintype ι] (len : ι → ℕ) (hlen : ∀ x, 1 ≤ len x)
    (c : ι → Fin m) (order : List ι) (hnodup : order.Nodup) (hall : ∀ x, x ∈ order)
    (hload : ∑ x, len x < m) :
    IsPlacement len (bottomUp len c order) ∧ CatalanNesting len (bottomUp len c order) := by sorry

end CatalanHashing.Dynamic
