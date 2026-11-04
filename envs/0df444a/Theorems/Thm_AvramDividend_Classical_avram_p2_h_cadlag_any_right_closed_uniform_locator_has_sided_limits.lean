-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_any_right_closed_uniform_locator_has_sided_limits
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_any_right_closed_uniform_locator_has_sided_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:08:05.933881+00:00
-- url     : https://prove2.me/theorems/985d94c1-6a12-44f7-aee6-3ca436c6c071
-- title:
--   Any uniformly shrinking right-closed cell locator has sided limits
-- statement:
--   Any integer-valued choice of a right-closed uniform cell containing a positive time gives lower endpoints tending strictly from the left and upper endpoints tending from the weak right, including exactly aligned time endpoints. Source exact cell duration and mesh-width convergence from pinned proved helpers.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_adjacent_duration
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_vanishing_width_halfopen_endpoints

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_any_right_closed_uniform_locator_has_sided_limits
    (T u : ℝ≥0) (j : ℕ → ℕ)
    (hj : ∀ n : ℕ,
      (j n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ (((j n + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1)))) :
    Tendsto (fun n : ℕ =>
      (j n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))
      atTop (𝓝[<] u) ∧
    Tendsto (fun n : ℕ =>
      (((j n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
      atTop (nhdsWithin u (Ici u)) := by sorry
