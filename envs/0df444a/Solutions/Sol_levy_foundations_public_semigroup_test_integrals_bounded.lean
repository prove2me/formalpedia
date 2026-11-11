-- Prove2me | solution 1 for levy_foundations_public_semigroup_test_integrals_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:24:02.824045+00:00
-- url     : https://prove2.me/submissions/42f167a5-91d8-4118-85e5-841bf7fcebce

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_mass_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Uniform scaled bounds for bounded tests supported away from zero follow
from the scaled mass estimate outside the support-free neighbourhood. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup)
    (f : BoundedContinuousFunction ℝ ℝ)
    (hf : ∃ r : ℝ, 0 < r ∧ ∀ x, |x| < r → f x = 0) :
    ∃ C : ℝ, ∀ t : {t : ℝ // 0 < t},
      |t.val⁻¹ * ∫ x, f x ∂(S.measure t : Measure ℝ)| ≤ C := by
  obtain ⟨r, hr, hfr⟩ := hf
  obtain ⟨Cmass, hmass⟩ :=
    levy_foundations_public_semigroup_scaled_largeSet_mass_bound S r hr
  refine ⟨‖f‖ * (Cmass : ℝ), ?_⟩
  intro t
  let μ : Measure ℝ := (S.measure t : Measure ℝ)
  haveI : IsProbabilityMeasure μ := (S.measure t).prop
  have hmeas : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have hcomp : {x : ℝ | |x| < r}ᶜ = largeSet r := by
    ext x
    change (¬ |x| < r) ↔ r ≤ |x|
    exact not_lt
  have hint : Integrable (fun x : ℝ => f x) μ :=
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (ae_of_all _ fun x => BoundedContinuousFunction.norm_coe_le_norm f x)
  have hzero : ∫ x in {x : ℝ | |x| < r}, f x ∂μ = 0 := by
    have heq : (∫ x in {x : ℝ | |x| < r}, f x ∂μ) =
        ∫ x in {x : ℝ | |x| < r}, (0 : ℝ) ∂μ :=
      setIntegral_congr_fun hmeas (fun x hx => hfr x hx)
    simpa using heq
  have hsplit : ∫ x, f x ∂μ = ∫ x in largeSet r, f x ∂μ := by
    have hs := integral_add_compl hmeas hint
    simpa only [hcomp, hzero, zero_add] using hs.symm
  have hnorm : ‖∫ x in largeSet r, f x ∂μ‖ ≤ ‖f‖ * μ.real (largeSet r) := by
    exact norm_setIntegral_le_of_norm_le_const
      (μ := μ) (s := largeSet r) (C := ‖f‖)
      (measure_lt_top _ _)
      (fun x hx => BoundedContinuousFunction.norm_coe_le_norm f x)
  have hmass_t := hmass t
  change t.val⁻¹ * (μ (largeSet r)).toReal ≤ (Cmass : ℝ) at hmass_t
  have hinv : 0 ≤ t.val⁻¹ := (inv_pos.mpr t.prop).le
  calc
    |t.val⁻¹ * ∫ x, f x ∂μ|
        = t.val⁻¹ * ‖∫ x in largeSet r, f x ∂μ‖ := by
          rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr t.prop), Real.norm_eq_abs]
    _ ≤ t.val⁻¹ * (‖f‖ * μ.real (largeSet r)) :=
        mul_le_mul_of_nonneg_left hnorm hinv
    _ = ‖f‖ * (t.val⁻¹ * (μ (largeSet r)).toReal) := by
        simp only [Measure.real_def]
        ring
    _ ≤ ‖f‖ * (Cmass : ℝ) :=
        mul_le_mul_of_nonneg_left hmass_t (norm_nonneg f)
