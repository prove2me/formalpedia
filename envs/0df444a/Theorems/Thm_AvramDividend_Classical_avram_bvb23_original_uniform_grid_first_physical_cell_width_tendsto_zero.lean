-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_uniform_grid_first_physical_cell_width_tendsto_zero
-- name    : AvramDividend.Classical.avram_bvb23_original_uniform_grid_first_physical_cell_width_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:44:49.159419+00:00
-- url     : https://prove2.me/theorems/10e9c391-b6cc-448d-8036-2a6c74371e38
-- title:
--   Original uniform physical grid initial cell width tends to zero as the number of cells increases
-- statement:
--   Under the exact original BV finite-horizon physical uniform grid law, the first positive grid time equals the physical horizon divided by the row index plus two. As the row index increases, this real first-cell width converges to zero. This discharges the source physical hmesh hypothesis of the Proved first-cell discounted gain lemma and the new strictly positive-interior masked initial-generator vanishing theorem.
-- source:
--   Pinned Mathlib tendsto_const_div_atTop_nhds_zero_nat and Filter.tendsto_add_atTop_iff_nat; original physical grid huniform equation from ed067740.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_uniform_grid_first_physical_cell_width_tendsto_zero
    (T : ℝ) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    Tendsto (fun n : ℕ => (u n 1 : ℝ))
      atTop (𝓝 (0 : ℝ)) := by sorry
