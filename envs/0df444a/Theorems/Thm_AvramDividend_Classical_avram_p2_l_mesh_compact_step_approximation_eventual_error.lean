-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_step_approximation_eventual_error
-- name    : AvramDividend.Classical.avram_p2_l_mesh_compact_step_approximation_eventual_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:23:31.297896+00:00
-- url     : https://prove2.me/theorems/153b828c-0357-4fb2-b6f1-136ad056a6bc
-- title:
--   Original mesh compact-test error controlled by one finite step approximation
-- statement:
--   For a cadlag source path, a strictly negative supported real test uniformly η-close to a finite interval-step test with endpoints avoiding significant intrinsic marks has original uniform-grid sums eventually within twice the significant-jump count times η of the true finite intrinsic jump sum. This exposes the only remaining compact-test approximation hypothesis explicitly and never assumes the desired convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_negative_test_difference_stability
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_intrinsic_finite_test_difference_stability
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_interval_simple_test_negative_support
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_original_interval_simple_test_sum_exact

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_compact_step_approximation_eventual_error {ι : Type*} [Fintype ι]
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (f : ℝ → ℝ) (hf : ∀ z : ℝ, -ρ < z → f z = 0)
    (a b c : ι → ℝ) (hb : ∀ i, b i ≤ -ρ)
    (hEndpoint : ∀ (i : ι) (u : ℝ≥0), 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ≠ a i ∧
        Y u - Function.leftLim Y u ≠ b i)
    (η : ℝ) (hη : 0 ≤ η)
    (hApprox : ∀ z : ℝ,
      |f z - (∑ i : ι,
        if z ∈ Ioc (a i) (b i) then c i else 0)| ≤ η) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop,
        |(∑ j ∈ Finset.range (n + 1),
          f (Y (((j + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) -
          (∑ u ∈ S, f (Y u - Function.leftLim Y u))| ≤
          2 * (S.card : ℝ) * η := by sorry
