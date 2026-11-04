-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:43:55.822204+00:00
-- url     : https://prove2.me/theorems/08858dc7-fb23-4027-a45b-3f74b8ddbb5a
-- title:
--   Original uniform Lévy grid compact-test sums converge to genuine jumps
-- statement:
--   For the genuine original uniform grid of nonnegative horizon T, the finite sum of a continuous compact jump-test applied to the actual path increments converges to the sum over a finite collection of genuine significant positive-time jumps. Assume the exact source càdlàg left/right regularity, a finite F capturing all marks at least rho on the closed horizon, positive-time support of F, and the test vanishing near zero. Construct original-grid selectors and bound, inject and identify terminally extended cells; prove the unmodified full-grid statement with no assumed jump-rate or compensator.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_selected_indices_in_grid
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_right_endpoint_squeeze
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_clamped_uniform_mesh_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_horizon_coverage
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
open Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_full_grid_compact_test_limit
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ) (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (hpos : ∀ t ∈ F, 0 < t)
    (hbound : ∀ t ∈ F, t ≤ T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        f (Y (((i + 1 : ℕ) : ℝ≥0) *
            (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
      atTop (𝓝 (∑ t ∈ F, f (Y t - Function.leftLim Y t))) := by sorry
