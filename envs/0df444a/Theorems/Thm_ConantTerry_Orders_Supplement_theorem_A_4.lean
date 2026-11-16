-- Prove2me | Theorems.Thm_ConantTerry_Orders_Supplement_theorem_A_4
-- name    : ConantTerry.Orders.Supplement.theorem_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:28:00.240451+00:00
-- url     : https://prove2.me/theorems/1f223997-d081-42d8-903b-01f6f129b66a
-- title:
--   Theorem A.4 — trees from non-uniform ladders
-- statement:
--   Let $X,Y$ be arbitrary sets, $f:X\times Y\to[0,1]$, $t\ge1$ and $\delta>0$. Then
--   $$
--   f\text{ admits a }(2^t,\delta)\text{-ladder}\quad\Longrightarrow\quad
--   f\text{ admits a }(t,\delta)\text{-tree}.
--   $$
--   The input ladder is the published non-uniform notion: its row thresholds may all differ, and the diagonal is high. The input length is exactly $2^t$, and the output has no scale loss. There is no finiteness, distinctness or regularity restriction on the ambient sets or labels.
--
--   This companion theorem supplies the reverse direction of the ladder–tree correspondence. It is not used in the proof of the goal Theorem 1.11.
--
--   Differences from the source:
--   - encoding: arbitrary sets X,Y and values in [0,1] → arbitrary types X,Y and the real subtype Set.Icc 0 1; reason: the subtype enforces exactly the source range and adds no finiteness, nonemptiness or regularity assumption
--   - encoding: finite binary words and 1-based finite indices → published List Bool word subtypes and zero-based Fin indices; reason: length, prefix, orientation and index inequalities are preserved by relabeling
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 22, Theorem A.4; proof pp. 22–23

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree
import Definitions.Def_ConantTerry_Orders_ladder

namespace ConantTerry.Orders.Supplement

/-- Theorem A.4, pp.22-23: non-uniform input, exact length 2^t, no scale loss. -/
theorem theorem_A_4 {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (t : ℕ) (ht : 1 ≤ t)
    (δ : ℝ) (hδ : 0 < δ) (hladder : AdmitsLadder f (2 ^ t) δ) :
    AdmitsTree f t δ := by sorry

end ConantTerry.Orders.Supplement
