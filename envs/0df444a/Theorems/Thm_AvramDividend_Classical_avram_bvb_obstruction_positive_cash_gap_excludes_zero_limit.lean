-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_positive_cash_gap_excludes_zero_limit
-- name    : AvramDividend.Classical.avram_bvb_obstruction_positive_cash_gap_excludes_zero_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:37:39.456788+00:00
-- url     : https://prove2.me/theorems/4d6d507e-d9f5-4a03-a26a-ba233b489808
-- title:
--   Positive limiting stopped-cash excess refutes vanishing original-grid positive error
-- statement:
--   If original stopped cash F_n tends to a, physical drift ledger L_n tends to zero, and a exceeds the initial candidate bound b, then the positive part max(F_n-b-L_n,0) cannot tend to zero. This isolates the limit contradiction required to disprove the zero-mark drift-only source leaf.
-- source:
--   Use Tendsto.sub, Tendsto.max, uniqueness of limits and positivity of a-b. This is mathematically unconditional and reusable with any source-exact pathwise cash/ledger limits.

import Mathlib
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.Hausdorff
open Filter
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_obstruction_positive_cash_gap_excludes_zero_limit (F L : ℕ → ℝ) (a b : ℝ) (hF : Tendsto F atTop (𝓝 a)) (hL : Tendsto L atTop (𝓝 (0 : ℝ))) (hgap : b < a) : ¬ Tendsto (fun n => max (F n - (b + L n)) 0) atTop (𝓝 (0 : ℝ)) := by sorry
