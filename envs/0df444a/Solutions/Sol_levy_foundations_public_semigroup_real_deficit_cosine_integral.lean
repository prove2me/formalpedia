-- Prove2me | solution 1 for levy_foundations_public_semigroup_real_deficit_cosine_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:32:51.200211+00:00
-- url     : https://prove2.me/submissions/f257de97-994f-4e9e-b368-4e43de047ddb

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal

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

/-- The semigroup real characteristic-function deficit equals a cosine integral. -/
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup)
    (t : {t : ℝ // 0 < t}) (ξ : ℝ) :
    (1 - Complex.exp ((t.val : ℂ) * S.exponent ξ)).re =
      ∫ x, (1 - Real.cos (ξ * x)) ∂(S.measure t : Measure ℝ) := by
  have hcf : charFun (S.measure t : Measure ℝ) ξ =
      exp ((t.val : ℂ) * S.exponent ξ) := by
    rw [show charFun (S.measure t : Measure ℝ) ξ =
      MeasureTheory.ProbabilityMeasure.characteristicFun (S.measure t) ξ from rfl]
    exact S.charFun_eq t ξ
  rw [← hcf]
  exact levy_foundations_aux_re_one_sub_charFun_eq_integral ξ
