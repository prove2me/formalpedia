-- Prove2me | solution 1 for levy_foundations_public_semigroup_second_moment_eventually_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:15:16.595422+00:00
-- url     : https://prove2.me/submissions/de312f92-029b-45e4-b87f-65e715cee408

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real
/-- Express the real part of a characteristic-function difference as a cosine integral. -/
private lemma levy_foundations_aux_integrable_charFun_integrand {μ : Measure ℝ} [IsFiniteMeasure μ] (ξ : ℝ) : Integrable (fun x : ℝ => exp ((↑(ξ * x) : ℂ) * I)) μ :=
  Integrable.of_bound
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id')).mul_const I
      |>.cexp.aestronglyMeasurable)
    1 (ae_of_all _ fun _ => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
/-- The real part of a characteristic-function difference equals a cosine integral. -/
private lemma levy_foundations_aux_re_one_sub_charFun_eq_integral {μ : Measure ℝ} [IsProbabilityMeasure μ] (ξ : ℝ) : (1 - charFun μ ξ).re = ∫ x, (1 - Real.cos (ξ * x)) ∂μ := by
  have hint := levy_foundations_aux_integrable_charFun_integrand (μ := μ) ξ
  have h1 : 1 - charFun μ ξ = ∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)) ∂μ := by
    have hcf : charFun μ ξ = ∫ x : ℝ, exp ((↑(ξ * x) : ℂ) * I) ∂μ := by
      rw [charFun_apply_real]; congr 1; ext x; congr 1; push_cast; ring
    rw [hcf]
    have h_one : (1 : ℂ) = ∫ _ : ℝ, (1 : ℂ) ∂μ := by simp [integral_const]
    conv_lhs => rw [h_one]
    exact (integral_sub (integrable_const (1 : ℂ)) hint).symm
  rw [h1, show (∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)) ∂μ).re = ∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)).re ∂μ from (integral_re (Integrable.sub (integrable_const 1) hint)).symm]
  congr 1; ext x
  simp only [sub_re, one_re, Complex.exp_ofReal_mul_I_re]
/-- Complex exponential first-order limit. -/
private lemma levy_foundations_aux_exp_first_order (z : ℂ) : Tendsto (fun t : ℝ => (exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 z) := by
  have hg : HasDerivAt (fun t : ℝ => cexp ((↑t : ℂ) * z)) z 0 := by
    have hf : HasDerivAt (fun t : ℝ => (↑t : ℂ) * z) (1 * z) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z
    have hexp := hf.cexp
    simp only [ofReal_zero, zero_mul, exp_zero, one_mul, one_mul] at hexp
    exact hexp
  have hslope := hg.tendsto_slope_zero
  simp only [zero_add, ofReal_zero, zero_mul, exp_zero] at hslope
  exact hslope.congr (fun t => by
    show t⁻¹ • (cexp ((↑t : ℂ) * z) - 1) = (cexp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)
    rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
    push_cast
    rw [inv_mul_eq_div]
    norm_cast)
/-- The scaled real-part exponential remainder converges to its derivative. -/
private lemma levy_foundations_aux_tendsto_inv_mul_re_one_sub_exp (z : ℂ) : Tendsto (fun t : ℝ => t⁻¹ * (1 - exp (↑t * z)).re) (𝓝[≠] 0) (𝓝 (-z).re) := by
  have h2 : Tendsto (fun t : ℝ => (1 - exp ((↑t : ℂ) * z)) / (↑t : ℂ)) (𝓝[≠] 0) (𝓝 (-z)) :=
    (levy_foundations_aux_exp_first_order z).neg.congr fun t => by
      show -((exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)) = _; ring
  have h3 := (Complex.continuous_re.tendsto _).comp h2
  exact h3.congr fun t => by
    simp only [Function.comp_def]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm,
        Complex.re_ofReal_mul]
/-- The small-jump moment is controlled by the cosine inequality. -/
private lemma levy_foundations_aux_small_moment_cosine_bound (S : ProbabilityTheory.ConvolutionSemigroup) (t : {t : ℝ // 0 < t}) : 2 / Real.pi ^ 2 * (t.val⁻¹ * ∫ x in ProbabilityTheory.smallSet, x ^ 2 ∂(S.measure t : Measure ℝ)) ≤ t.val⁻¹ * (1 - exp (↑t.val * S.exponent 1)).re := by
  have hsmallMeas : MeasurableSet ProbabilityTheory.smallSet := (isOpen_Iio.preimage continuous_abs).measurableSet
  have hsmall_iff (x : ℝ) : x ∈ ProbabilityTheory.smallSet ↔ |x| < 1 := Iff.rfl
  have hcf : charFun (S.measure t : Measure ℝ) 1 = exp (↑t.val * S.exponent 1) := by
    rw [show charFun (S.measure t : Measure ℝ) 1 = MeasureTheory.ProbabilityMeasure.characteristicFun (S.measure t) 1 from rfl]
    exact S.charFun_eq t 1
  have hre : (1 - exp (↑t.val * S.exponent 1)).re = ∫ x, (1 - Real.cos (1 * x)) ∂(S.measure t : Measure ℝ) := by
    rw [← hcf]
    exact levy_foundations_aux_re_one_sub_charFun_eq_integral 1
  rw [hre]
  simp only [one_mul]
  rw [show 2 / Real.pi ^ 2 * (t.val⁻¹ * ∫ x in ProbabilityTheory.smallSet, x ^ 2 ∂(S.measure t : Measure ℝ)) = t.val⁻¹ * (2 / Real.pi ^ 2 * ∫ x in ProbabilityTheory.smallSet, x ^ 2 ∂(S.measure t : Measure ℝ)) from by ring]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr t.prop))
  have hpi_bound : ∀ x : ℝ, x ∈ ProbabilityTheory.smallSet → 2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
    intro x hx
    have hxp : |x| ≤ Real.pi :=
      le_trans (le_of_lt ((hsmall_iff x).mp hx))
        (le_trans (by norm_num : (1 : ℝ) ≤ 2) Real.two_le_pi)
    linarith [Real.cos_le_one_sub_mul_cos_sq hxp]
  have hint_sq : IntegrableOn (fun x => 2 / Real.pi ^ 2 * x ^ 2) ProbabilityTheory.smallSet (S.measure t : Measure ℝ) :=
    Integrable.of_bound
      ((continuous_const.mul (continuous_pow 2)).aestronglyMeasurable)
      (2 / Real.pi ^ 2)
      (by filter_upwards
          [ae_restrict_mem hsmallMeas] with x hx
          have habs : |x| < 1 := (hsmall_iff x).mp hx
          have hx_sq : x ^ 2 ≤ 1 := by
            nlinarith [sq_abs x,
              mul_le_of_le_one_right (abs_nonneg x) habs.le]
          rw [Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg x))]
          calc 2 / Real.pi ^ 2 * x ^ 2
              ≤ 2 / Real.pi ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left hx_sq (by positivity)
            _ = 2 / Real.pi ^ 2 := mul_one _)
  have hint_cos : IntegrableOn (fun x => 1 - Real.cos x) ProbabilityTheory.smallSet (S.measure t : Measure ℝ) :=
    (Integrable.of_bound
      ((continuous_const.sub Real.continuous_cos).aestronglyMeasurable)
      2 (ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, Pi.sub_apply,
          abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one x))]
        linarith [Real.neg_one_le_cos x])).integrableOn
  calc 2 / Real.pi ^ 2 * ∫ x in ProbabilityTheory.smallSet, x ^ 2 ∂(S.measure t : Measure ℝ) = ∫ x in ProbabilityTheory.smallSet, 2 / Real.pi ^ 2 * x ^ 2 ∂(S.measure t : Measure ℝ) := (integral_const_mul _ _).symm
    _ ≤ ∫ x in ProbabilityTheory.smallSet, (1 - Real.cos x)
          ∂(S.measure t : Measure ℝ) :=
        setIntegral_mono_on hint_sq hint_cos
          hsmallMeas hpi_bound
    _ ≤ ∫ x, (1 - Real.cos x) ∂(S.measure t : Measure ℝ) :=
        setIntegral_le_integral
          (Integrable.of_bound
            ((continuous_const.sub Real.continuous_cos).aestronglyMeasurable)
            2 (ae_of_all _ fun x => by
              simp only [Real.norm_eq_abs,
                abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one x))]
              linarith [Real.neg_one_le_cos x]))
          (ae_of_all _ fun x => sub_nonneg.mpr (Real.cos_le_one _))
/-- Eventual quadratic moment bound from the cosine estimate. -/ theorem solution (S : ProbabilityTheory.ConvolutionSemigroup) {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (t_seq n).val⁻¹ * ∫ x in ProbabilityTheory.smallSet, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ) ≤ C := by
  set L := (-(S.exponent 1)).re
  have htend : Tendsto
      (fun (t : ℝ) => t⁻¹ * (1 - exp ((t : ℂ) * S.exponent 1)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    (levy_foundations_aux_tendsto_inv_mul_re_one_sub_exp
      (S.exponent 1)).mono_left
        (nhdsWithin_mono (0 : ℝ) fun _ hx => ne_of_gt hx)
  have hevt : ∀ᶠ (r : ℝ) in 𝓝[>] (0 : ℝ),
      r⁻¹ * (1 - exp ((r : ℂ) * S.exponent 1)).re ≤ |L| + 1 :=
    (htend.eventually (Iio_mem_nhds (by linarith [le_abs_self L]))).mono
      fun _ h => le_of_lt h
  have ht_filter : Tendsto t_seq atTop
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    rw [Filter.tendsto_comap_iff]
    exact tendsto_nhdsWithin_iff.mpr
      ⟨ht, Filter.Eventually.of_forall (fun n => (t_seq n).prop)⟩
  refine ⟨Real.pi ^ 2 / 2 * (|L| + 1), by positivity, ?_⟩
  have hbound_t :
      ∀ᶠ (t : {t : ℝ // 0 < t}) in Filter.comap Subtype.val (𝓝[>] (0 : ℝ)),
        t.val⁻¹ * ∫ x in ProbabilityTheory.smallSet, x ^ 2 ∂(S.measure t : Measure ℝ)
          ≤ Real.pi ^ 2 / 2 * (|L| + 1) := by
    exact (hevt.comap Subtype.val).mono fun t ht => by
      have hle := le_trans (levy_foundations_aux_small_moment_cosine_bound S t) ht
      have hfactor := mul_le_mul_of_nonneg_left hle
        (show (0 : ℝ) ≤ Real.pi ^ 2 / 2 from by positivity)
      rw [← mul_assoc,
        show Real.pi ^ 2 / 2 * (2 / Real.pi ^ 2) = 1 from by
          field_simp,
        one_mul] at hfactor
      exact hfactor
  exact ht_filter.eventually hbound_t
