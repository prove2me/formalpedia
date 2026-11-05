-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_full_grid_local_mark_continuity
-- name    : AvramDividend.Classical.avram_p2_l_mesh_full_grid_local_mark_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:27:31.318692+00:00
-- url     : https://prove2.me/theorems/4edb087f-8409-437e-b57f-6d99d0eabeb2
-- title:
--   Full original cadlag mesh-to-intrinsic-jump convergence for tests continuous only at large actual marks
-- statement:
--   For a real cadlag path, a test vanishing near zero whose only assumed continuity is at the finitely many significant actual jump marks, show original full right-closed uniform-grid marked sums converge to the true finite intrinsic jump sum. This strengthens the global-continuity P2-H theorem and permits boundary-qualified Borel indicators after proving local indicator continuity at each actual mark. No convergence claim for arbitrary Borel sets.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_jump_test_local_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_any_right_closed_uniform_locator_has_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_grid_sum_eq_selected_injective_cells

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_l_mesh_full_grid_local_mark_continuity
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hfzero : ∀ z : ℝ, |z| < ρ → f z = 0)
    (hf : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      ContinuousAt f (Y u - Function.leftLim Y u))
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
