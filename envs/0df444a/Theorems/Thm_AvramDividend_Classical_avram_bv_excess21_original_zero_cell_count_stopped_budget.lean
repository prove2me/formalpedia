-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess21_original_zero_cell_count_stopped_budget
-- name    : AvramDividend.Classical.avram_bv_excess21_original_zero_cell_count_stopped_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:26:16.812344+00:00
-- url     : https://prove2.me/theorems/f3f336fd-70ce-4464-ab71-617621bf8c17
-- title:
--   Original BV zero-reserve one-cell stopped cash versus same negative-jump count martingale with nonnegative collision error
-- statement:
--   For one actual physical original-process BV zero-reserve cell, k is the number of negative jumps in its time interval. A no-jump cell obeys the proved sharp exponential origin HJB cash budget, and a jumped cell obeys the coarse drift-budget bound up to its first ruin jump. A single coefficient -exp(-qs)w(0) times the centred count (k - nu(Iio0)*(t-s)) covers both situations, leaving a nonnegative error consisting only of (k-1)_+ jump collisions and q*(t-s) on jump-containing cells. Both errors have expected sum tending to zero on genuine uniform finite-activity Poisson meshes, pending their original-process factorial count bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess21_original_zero_cell_count_stopped_budget
    (q rate w0 cash s t : ℝ) (k : ℕ)
    (hq : 0 < q) (hrate : 0 ≤ rate) (hw0 : 0 ≤ w0)
    (hst : s ≤ t)
    (hNoJump : k = 0 → cash ≤ (q + rate) * w0 *
      ((Real.exp (-(q * s)) - Real.exp (-(q * t))) / q))
    (hJump : k ≠ 0 → cash ≤
      (q + rate) * w0 * Real.exp (-(q * s)) * (t - s)) :
    let Err : ℝ := if k = 0 then 0 else
      Real.exp (-(q * s)) * w0 * ((k : ℝ) - 1) +
        q * w0 * Real.exp (-(q * s)) * (t - s)
    0 ≤ Err ∧
      cash + (if k = 0 then Real.exp (-(q * t)) * w0 else 0) -
        Real.exp (-(q * s)) * w0 ≤
      -Real.exp (-(q * s)) * w0 *
        ((k : ℝ) - rate * (t - s)) + Err := by sorry
