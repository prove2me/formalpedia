-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_uniform_grid_cofinal_index_le_physical_horizon
-- name    : AvramDividend.Classical.avram_bvb22_original_uniform_grid_cofinal_index_le_physical_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:43:36.037909+00:00
-- url     : https://prove2.me/theorems/7a37b233-0669-4171-9851-170d030ab112
-- title:
--   Original uniform finite-horizon grid indices are bounded by physical horizon
-- statement:
--   Every original uniform physical grid point with index at most one beyond the current cell count lies within the nonnegative fixed finite horizon. This supplies the exact bounded-index premise of the already Proved original zero-jump BV residual theorem.
-- source:
--   Elementary real arithmetic on the source physical grid T*i/(n+2).

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_uniform_grid_cofinal_index_le_physical_horizon
    (T : ℝ) (hT : 0 ≤ T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n i : ℕ) (hi : i ≤ n + 1) :
    u n i ≤ (⟨T, hT⟩ : ℝ≥0) := by sorry
