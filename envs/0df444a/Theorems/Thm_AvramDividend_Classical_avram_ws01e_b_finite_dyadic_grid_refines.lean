-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finite_dyadic_grid_refines
-- name    : AvramDividend.Classical.avram_ws01e_b_finite_dyadic_grid_refines
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:58:55.989027+00:00
-- url     : https://prove2.me/theorems/d127a02f-9a16-42c3-94c6-7698b71bc70f
-- title:
--   Finite-horizon dyadic observation grids are nested under doubling the mesh index
-- statement:
--   For any finite nonnegative horizon T, every point indexed k≤2^n on the dyadic time grid at level n is exactly the point indexed 2k≤2^(n+1) on the next grid. This gives nested finite observation events, permitting continuity from below for the laws of Lévy maxima and drawdowns.
-- source:
--   Elementary dyadic grid refinement. Used to apply Mathlib Monotone.measure_iUnion in the continuous-horizon limit of finite-grid Lévy reversal, without unproved Wiener–Hopf factorisation.

import Mathlib
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_finite_dyadic_grid_refines (T : ℝ≥0) (n : ℕ)
    (k : Fin ((2 : ℕ) ^ n + 1)) :
    ∃ j : Fin ((2 : ℕ) ^ (n + 1) + 1),
      ((j.val : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1)) * T =
      ((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * T := by sorry
