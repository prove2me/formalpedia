-- Prove2me | solution 1 for levy_foundations_public_semigroup_tilted_mass_along_seq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:49:51.562362+00:00
-- url     : https://prove2.me/submissions/03aa7eb9-c457-4c20-83f8-6004dab2af4b

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_second_moment_eventually_bounded
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_mass_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Square integrability on the open unit ball for any finite measure. -/
private lemma levy_public_sq_integrableOn_smallSet (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IntegrableOn (fun x => x ^ 2) smallSet μ := by
  have hsmall_meas : MeasurableSet smallSet :=
    (isOpen_Iio.preimage continuous_abs).measurableSet
  refine IntegrableOn.of_bound (measure_lt_top _ _) ?_ 1 ?_
  · exact ((continuous_pow 2).measurable.aemeasurable.aestronglyMeasurable).restrict
  · exact (ae_restrict_mem hsmall_meas).mono (fun x hx => by
      have hxlt : |x| < 1 := hx
      simp only [Real.norm_eq_abs]
      have h2 : x ^ 2 < 1 := by
        have h3 : |x| ^ 2 < 1 := pow_lt_one₀ (abs_nonneg x) hxlt two_ne_zero
        rwa [sq_abs] at h3
      rw [abs_of_nonneg (sq_nonneg x)]
      linarith)

theorem solution (S : ProbabilityTheory.ConvolutionSemigroup)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (hseq : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ n in atTop, S.tiltedScaledMeasure (t_seq n) Set.univ ≤ (C : ℝ≥0∞) := by
  obtain ⟨C₂, hC₂_pos, hC₂⟩ := levy_foundations_public_semigroup_second_moment_eventually_bounded S hseq
  obtain ⟨C_large, hC_large⟩ := levy_foundations_public_semigroup_scaled_largeSet_mass_bound S 1 one_pos
  refine ⟨C₂.toNNReal + C_large + 1, zero_lt_one.trans_le le_add_self, ?_⟩
  have hsmall_meas : MeasurableSet smallSet :=
    (isOpen_Iio.preimage continuous_abs).measurableSet
  have hsmall_compl : smallSet = (largeSet 1)ᶜ := by
    ext x
    simp [smallSet, largeSet, not_le]
  filter_upwards [hC₂] with n ht
  let t := t_seq n
  haveI : IsProbabilityMeasure (S.measure t : Measure ℝ) := (S.measure t).prop
  have hA : ∫⁻ x in smallSet, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
      ≤ ENNReal.ofReal C₂ := by
    have hfg : Set.EqOn (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)))
        (fun x => ENNReal.ofReal (x ^ 2)) smallSet := by
      intro x hx
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, (show |x| < 1 from hx)]
      simp [min_eq_right hx2]
    rw [setLIntegral_congr_fun hsmall_meas hfg]
    simp only [ProbabilityTheory.ConvolutionSemigroup.scaledMeasure]
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
        ← ofReal_integral_eq_lintegral_ofReal (levy_public_sq_integrableOn_smallSet (S.measure t : Measure ℝ))
          (ae_of_all _ fun x => sq_nonneg x),
        ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr t.prop))]
    exact ENNReal.ofReal_le_ofReal ht
  have hB : ∫⁻ x in smallSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
      ≤ ENNReal.ofReal (C_large : ℝ) := by
    have hle1 : ∫⁻ x in smallSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
        ≤ S.scaledMeasure t smallSetᶜ := by
      calc ∫⁻ x in smallSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
          ≤ ∫⁻ _ in smallSetᶜ, 1 ∂(S.scaledMeasure t) :=
            lintegral_mono (fun x => ENNReal.ofReal_le_one.mpr (min_le_left _ _))
        _ = S.scaledMeasure t smallSetᶜ := setLIntegral_one _
    refine hle1.trans ?_
    rw [hsmall_compl, compl_compl]
    have hscaled : S.scaledMeasure t (largeSet 1) ≤ ENNReal.ofReal (C_large : ℝ) := by
      change ENNReal.ofReal t.val⁻¹ * (S.measure t : Measure ℝ) (largeSet 1) ≤ _
      rw [show (S.measure t : Measure ℝ) (largeSet 1) =
          ENNReal.ofReal ((S.measure t : Measure ℝ) (largeSet 1)).toReal from
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,
        ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr t.prop))]
      exact ENNReal.ofReal_le_ofReal (hC_large t)
    exact hscaled
  have hmass : S.tiltedScaledMeasure t Set.univ
      = ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t) := by
    rw [show S.tiltedScaledMeasure t = (S.scaledMeasure t).withDensity
          (fun x => ENNReal.ofReal (min 1 (x ^ 2))) from rfl,
      withDensity_apply _ MeasurableSet.univ]
    exact setLIntegral_univ _
  have hsplit : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
      = ∫⁻ x in smallSet, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
        + ∫⁻ x in smallSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t) :=
    (lintegral_add_compl _ hsmall_meas).symm
  rw [hmass, hsplit]
  calc ∫⁻ x in smallSet, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
        + ∫⁻ x in smallSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
      ≤ ENNReal.ofReal C₂ + ENNReal.ofReal (C_large : ℝ) := add_le_add hA hB
    _ ≤ ((C₂.toNNReal + C_large + 1 : ℝ≥0) : ℝ≥0∞) := by
        have e1 : ENNReal.ofReal C₂ = (↑C₂.toNNReal : ℝ≥0∞) := rfl
        have e2 : ENNReal.ofReal (C_large : ℝ) = (↑C_large : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
        rw [e1, e2, ENNReal.coe_add, ENNReal.coe_add, ENNReal.coe_one]
        exact le_self_add
