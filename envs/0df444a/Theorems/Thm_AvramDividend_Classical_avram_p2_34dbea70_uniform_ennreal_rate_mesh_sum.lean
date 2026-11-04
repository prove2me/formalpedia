-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_ennreal_rate_mesh_sum
-- name    : AvramDividend.Classical.avram_p2_34dbea70_uniform_ennreal_rate_mesh_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:09:24.602362+00:00
-- url     : https://prove2.me/theorems/e0aaf6e7-4fd3-4f5f-b491-e10199fa0d44
-- title:
--   Finite ENNReal sum of constant-rate uniform mesh cells equals C times horizon
-- statement:
--   For nonnegative time T and rate C, the sum in ENNReal over all n+1 uniform-grid cells of the NNReal products C*T/(n+1) equals the ENNReal embedding of C*T. This follows by casting an exact NNReal sum and is used to bound the source expected negative marked grid count uniformly in n.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_width_sum

open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_uniform_ennreal_rate_mesh_sum
    (T C : ℝ≥0) (n : ℕ) :
    (∑ _i ∈ Finset.range (n + 1),
      ((C * (T / ((n : ℝ≥0) + 1)) : ℝ≥0) : ℝ≥0∞)) =
        ((C * T : ℝ≥0) : ℝ≥0∞) := by sorry
