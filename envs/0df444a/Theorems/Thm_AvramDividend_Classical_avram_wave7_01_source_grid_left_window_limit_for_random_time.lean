-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_grid_left_window_limit_for_random_time
-- name    : AvramDividend.Classical.avram_wave7_01_source_grid_left_window_limit_for_random_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:00:47.029249+00:00
-- url     : https://prove2.me/theorems/33dfcfee-fe1a-4d17-bc79-dbbdfde8e650
-- title:
--   Shrinking one-sided source-clock lower grid windows converge to their candidate time
-- statement:
--   For any original nonnegative source-clock jump time and any nonnegative radius sequence tending to zero, the truncated lower endpoints t-ε_n tend to t. This supplies the exact hLower premise for the accepted two-grid marked-jump Borel extension, including all initial-window saturation at zero.
-- source:
--   Filter.Tendsto.sub for the ContinuousSub instance on NNReal and tsub_zero in pinned Mathlib.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_source_grid_left_window_limit_for_random_time
    (t : ℝ≥0) (ε : ℕ → ℝ≥0)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => t - ε n) atTop (𝓝 t) := by sorry
