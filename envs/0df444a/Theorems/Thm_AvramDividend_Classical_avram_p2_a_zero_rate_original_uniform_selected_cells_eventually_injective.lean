-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:21:50.485584+00:00
-- url     : https://prove2.me/theorems/bd4bfbea-58bf-4109-b15e-6b9e8f767859
-- title:
--   Original finite jump selectors eventually injective on uniform source mesh
-- statement:
--   Any finite family of selected genuine original Lévy jump cells has eventually pairwise distinct original uniform-grid indices. Use the accepted mesh-width limit and right endpoint squeezing to establish convergence of selected right endpoints to their distinct jump times, then the accepted finite-family eventual-index-injectivity theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_crossing_right_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective
    (T : ℝ≥0) (F : Finset ℝ≥0) (idx : ℝ≥0 → ℕ → ℕ)
    (hcell : ∀ t ∈ F, ∀ n,
      (idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
      t ≤ (((idx t n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1)))) :
    ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun t => idx t n) (F : Set ℝ≥0) := by sorry
