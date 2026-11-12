-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB71_common_refinement_coarse_start_le_fine_start
-- name    : AvramDividend.Classical.avram_gbB71_common_refinement_coarse_start_le_fine_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:55:51.769939+00:00
-- url     : https://prove2.me/theorems/48d9d01b-1d05-44e6-a87f-6fa6c991ed47
-- title:
--   Uniform product-refinement coarse coefficient is observed before the fine-grid step
-- statement:
--   For arbitrary positive natural mesh denominators, product-refining two nonnested Gaussian grids produces a fine cell whose left endpoint is at or later than its parent coarse-grid left endpoint. This inequality transports the original right-continuous filtration measurability of coarse coefficients to each fine subcell.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB71_common_refinement_coarse_start_le_fine_start
    (r m p : ℕ) (n : ℝ≥0) :
    (((r / (p + 1) : ℕ) : ℝ≥0) *
      (n / ((m + 1 : ℕ) : ℝ≥0))) ≤
      (r : ℝ≥0) *
        (n / (((m + 1) * (p + 1) : ℕ) : ℝ≥0)) := by sorry
