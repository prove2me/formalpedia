-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a30_horizon_final_cell_left_strict
-- name    : AvramDividend.Classical.avram_ga_a30_horizon_final_cell_left_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:26:42.881927+00:00
-- url     : https://prove2.me/theorems/913e0f78-67fe-48ce-875d-e91371902a5d
-- title:
--   Final physical uniform-mesh left endpoint is strictly before positive horizon
-- statement:
--   At every mesh index m the final left endpoint m n/(m+1) lies strictly before the positive horizon n. The exact identity is needed for the original physical postpayment compact reserve bound at the stop-straddling horizon cell.
-- source:
--   Root-connected horizon-boundary child ad246ef2; combines with Proved gledger137 compact postpayment band, fdfb0b39 final right endpoint equals horizon and 85dd6f23 original path increment limit.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a30_horizon_final_cell_left_strict
    (n : ℝ≥0) (hn : 0 < n) (m : ℕ) :
    (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) < n := by sorry
