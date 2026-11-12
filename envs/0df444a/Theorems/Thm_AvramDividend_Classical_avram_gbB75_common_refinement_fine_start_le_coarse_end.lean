-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB75_common_refinement_fine_start_le_coarse_end
-- name    : AvramDividend.Classical.avram_gbB75_common_refinement_fine_start_le_coarse_end
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:40:20.573465+00:00
-- url     : https://prove2.me/theorems/14ccc9d3-40c5-4efd-87a2-fb87134094ab
-- title:
--   Fine-grid time lies before the next coarse-grid endpoint in a uniform product refinement
-- statement:
--   For two arbitrary nonnested uniform meshes with natural denominators m+1 and p+1, the common product-refinement cell beginning at fine index r lies no later than the right endpoint of the containing coarse cell. Together with the Proved coarse-start lower bound B71, this brackets original postpayment sample times for coefficient convergence in B61.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB75_common_refinement_fine_start_le_coarse_end
    (r m p : ℕ) (n : ℝ≥0) :
    (r : ℝ≥0) *
      (n / (((m + 1) * (p + 1) : ℕ) : ℝ≥0)) ≤
      (((r / (p + 1) + 1 : ℕ) : ℝ≥0) *
        (n / ((m + 1 : ℕ) : ℝ≥0))) := by sorry
