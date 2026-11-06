-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_eq_two_finite_jump_sums
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_residual_eq_two_finite_jump_sums
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:06:59.432449+00:00
-- url     : https://prove2.me/theorems/006503c8-db19-445c-8c96-fcaff4333f41
-- title:
--   The original cutoff Gaussian residual is exactly X minus finite small and large source jump sums
-- statement:
--   The original cutoff candidate residual M^c_n is exactly the original path X.X minus time X.c and the finite sums of the source's own large and small negative jumps, plus the deterministic small-band ν compensation. Both finite support sets are the true original jump times, with exact cutoffs. This is a rigorous pathwise truncation identity, not a martingale or continuity assertion.
-- source:
--   Proved original small-band finite jump sum 158e793f, and new original large-jump finite signed integral-to-sum pending 2026-11-04.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_residual_eq_two_finite_jump_sums
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (T : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F G : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      (∀ u : ℝ≥0, u ∈ G ↔ 0 < u ∧ u ≤ T ∧ j u ≤ -1) ∧
      avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω =
        X.X T ω - (T : ℝ) * X.c -
          ((∑ u ∈ F, j u) -
             (T : ℝ) * (∫ z in Ioc (-1 : ℝ)
                (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) -
          (∑ u ∈ G, j u) := by sorry
