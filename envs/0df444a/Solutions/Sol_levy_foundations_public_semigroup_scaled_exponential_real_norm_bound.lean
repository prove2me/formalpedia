-- Prove2me | solution 1 for levy_foundations_public_semigroup_scaled_exponential_real_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:47:55.447914+00:00
-- url     : https://prove2.me/submissions/b5c7255e-8403-4e82-9d7c-1e28d67c1df5

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal

/-- The scaled real deficit of the semigroup exponential is bounded
uniformly in time by twice the characteristic exponent norm. -/
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup)
    (t : {t : ℝ // 0 < t}) (ξ : ℝ) :
    t.val⁻¹ * (1 - Complex.exp ((t.val : ℂ) * S.exponent ξ)).re ≤
      2 * ‖S.exponent ξ‖ := by
  have hexp_le1 : ‖exp ((t.val : ℂ) * S.exponent ξ)‖ ≤ 1 := by
    haveI : IsProbabilityMeasure (S.measure t : Measure ℝ) := (S.measure t).prop
    have h := norm_charFun_le_one (μ := (S.measure t : Measure ℝ)) ξ
    change ‖(S.measure t).characteristicFun ξ‖ ≤ 1 at h
    rwa [S.charFun_eq t ξ] at h
  have hre_le2 : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 := by
    have hge : -1 ≤ (exp ((t.val : ℂ) * S.exponent ξ)).re := by
      have h1 : |(exp ((t.val : ℂ) * S.exponent ξ)).re| ≤ 1 :=
        (Complex.abs_re_le_norm _).trans hexp_le1
      linarith [neg_abs_le (exp ((t.val : ℂ) * S.exponent ξ)).re]
    simp only [sub_re, one_re]; linarith
  by_cases h : t.val * ‖S.exponent ξ‖ ≤ 1
  · -- Small regime: use norm_exp_sub_one_le
    have htz : ‖(t.val : ℂ) * S.exponent ξ‖ ≤ 1 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; exact h
    have h_re : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * t.val * ‖S.exponent ξ‖ :=
      calc (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ ‖1 - exp ((t.val : ℂ) * S.exponent ξ)‖ := Complex.re_le_norm _
        _ = ‖exp ((t.val : ℂ) * S.exponent ξ) - 1‖ := norm_sub_rev _ _
        _ ≤ 2 * ‖(t.val : ℂ) * S.exponent ξ‖ := Complex.norm_exp_sub_one_le htz
        _ = 2 * t.val * ‖S.exponent ξ‖ := by
              simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; ring
    calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
        ≤ t.val⁻¹ * (2 * t.val * ‖S.exponent ξ‖) :=
            mul_le_mul_of_nonneg_left h_re (le_of_lt (inv_pos.mpr t.prop))
      _ = 2 * ‖S.exponent ξ‖ := by field_simp [ne_of_gt t.prop]

  · -- Large regime: t⁻¹ ≤ ‖ψ(ξ)‖, use (1-exp).re ≤ 2
    push Not at h
    have hψ_pos : (0 : ℝ) < ‖S.exponent ξ‖ := by
      rcases ne_or_eq (S.exponent ξ) 0 with hne | h0
      · exact norm_pos_iff.mpr hne
      · simp only [h0, norm_zero] at h; linarith
    have ht_inv : t.val⁻¹ ≤ ‖S.exponent ξ‖ :=
      (inv_le_iff_one_le_mul₀' t.prop).mpr (le_of_lt h)
    calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
        ≤ t.val⁻¹ * 2 :=
            mul_le_mul_of_nonneg_left hre_le2 (le_of_lt (inv_pos.mpr t.prop))
      _ ≤ ‖S.exponent ξ‖ * 2 := by nlinarith
      _ = 2 * ‖S.exponent ξ‖ := by ring
