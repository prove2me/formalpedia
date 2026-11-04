-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_sum_tends_to_all_large_actual_jumps
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_uniform_test_sum_tends_to_all_large_actual_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:27:58.98512+00:00
-- url     : https://prove2.me/theorems/9bb673ea-ccfe-4756-a1a0-0fca5ed1c1cd
-- title:
--   Exact uniform grid test sum tends to finite actual large-jump sum
-- statement:
--   For a right-continuous real path with all strict left limits on nonnegative times, and a continuous test function zero around the origin, prove exact original uniform right-closed grid-sum convergence to the finite sum over every actual jump above the test separation threshold. The finite actual set includes jumps at zeros of the test, preventing a false eventual-support claim. No rate, expectation, compensator or process construction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_actual_jump_cell_test_sum_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_any_right_closed_uniform_locator_has_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_grid_sum_eq_selected_injective_cells

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_h_cadlag_uniform_test_sum_tends_to_all_large_actual_jumps
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hfzero : ∀ z : ℝ, |z| < ρ → f z = 0)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S, f (Y u - Function.leftLim Y u))) := by sorry
