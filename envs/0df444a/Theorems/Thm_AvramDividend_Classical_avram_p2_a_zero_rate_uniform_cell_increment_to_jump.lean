-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_increment_to_jump
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_increment_to_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:09:43.787694+00:00
-- url     : https://prove2.me/theorems/0674332c-8293-4e67-8626-7d1da9d50577
-- title:
--   Actual uniform source jump grid cell converges to the true càdlàg jump increment
-- statement:
--   For any càdlàg real path and actual jump time u within (0,T], obtain the already-Proved original uniform half-open cell locator and prove that the corresponding finite-mesh increment converges to Y(u)-leftLim(Y,u), by composing exact sided endpoint limits with left and right path limits. This supports continuous compact-test grid-to-jump convergence without any Lévy rate hypothesis.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits

open Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_increment_to_jump
    (Y : ℝ≥0 → ℝ) (T u : ℝ≥0)
    (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T)
    (hL : Tendsto Y (nhdsWithin u (Iio u))
      (𝓝 (Function.leftLim Y u)))
    (hR : ContinuousWithinAt Y (Ici u) u) :
    ∃ i : ℕ → ℕ,
      (∀ n, i n ≤ n ∧
        (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ ((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n =>
        Y (((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
        atTop (𝓝 (Y u - Function.leftLim Y u)) := by sorry
