-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB183_uniform_physical_grid_step_fits_centered_long_tube
-- name    : AvramDividend.Classical.avram_gbB183_uniform_physical_grid_step_fits_centered_long_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T19:11:51.869963+00:00
-- url     : https://prove2.me/theorems/40bf21cf-ba27-4281-bb11-1f982ee6600a
-- title:
--   Finite uniform physical grid step fits longer Brownian tube with positive overshoot margin
-- statement:
--   For a natural physical-grid span n and resolution m with m+1≥16000n, a time T=1/1000 plus the physical uniform mesh Δ=n/(m+1) stays inside the slightly longer Brownian tube horizon 17/16000. This is the exact arithmetic link needed to transfer centered Brownian path bounds through the overshoot cell and establish original physical G/H L1 noise on the positive-probability event.

import Mathlib
open MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB183_uniform_physical_grid_step_fits_centered_long_tube
    (n m : ℕ) (hm : 16000 * n ≤ m + 1) :
    (1 / 1000 : ℝ≥0) +
      (n : ℝ≥0) / ((m : ℝ≥0) + 1) ≤
      (17 / 16000 : ℝ≥0) := by sorry
