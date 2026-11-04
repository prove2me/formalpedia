-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
-- name    : AvramDividend.Classical.avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:20:15.508191+00:00
-- url     : https://prove2.me/theorems/4a76a7f1-f017-4feb-85a5-d1745fb5e417
-- title:
--   Original nonnegative uniform horizon mesh width tends to zero
-- statement:
--   For every nonnegative horizon T, the cell widths T divided by n+1 of the actual uniform right-closed grid tend to zero in nonnegative real time. This is the quantitative prerequisite for turning the previously verified half-open cell locator into correctly sided shrinking endpoints around every genuine source jump.

import Mathlib

open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => T / ((n : ℝ≥0) + 1)) atTop (𝓝 (0 : ℝ≥0)) := by sorry
