-- Prove2me | solution 1 for levy_foundations_compensatedIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:09:58.494839+00:00
-- url     : https://prove2.me/submissions/b9e5aa15-c474-4f98-8ef1-c3365bf2f8ca

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_compensatedIntegrand

open MeasureTheory

open LevyFoundations in
theorem cad_bound (ξ x R : ℝ) (hξ : |ξ| ≤ R) :
    ‖compensatedIntegrand ξ x‖ ≤ (3 * R ^ 2 + 2) * min 1 (x ^ 2) := by
  have hR : 0 ≤ R := (abs_nonneg ξ).trans hξ
  have hξ2 : ξ ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_abs ξ, abs_nonneg ξ]
  unfold compensatedIntegrand
  by_cases h : |x| < 1
  · have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    rw [min_eq_right hx2]
    simp only [h, if_true, mul_one]
    have hw : ‖((x * ξ : ℝ) : ℂ) * Complex.I‖ = |x * ξ| := by simp
    have hy : (x * ξ) ^ 2 ≤ R ^ 2 * x ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg x]
    have heq : Complex.exp ((x : ℂ) * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I
        = Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 - ((x * ξ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring_nf
    rw [heq]
    by_cases hy1 : |x * ξ| ≤ 1
    · have := Complex.norm_exp_sub_one_sub_id_le (x := ((x * ξ : ℝ) : ℂ) * Complex.I) (by rw [hw]; exact hy1)
      rw [hw, sq_abs] at this
      nlinarith [sq_nonneg x, sq_nonneg R]
    · rw [not_le] at hy1
      have h1 : ‖Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1 - ((x * ξ : ℝ) : ℂ) * Complex.I‖
          ≤ 1 + 1 + |x * ξ| := by
        calc _ ≤ ‖Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I) - 1‖
              + ‖((x * ξ : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
          _ ≤ (‖Complex.exp (((x * ξ : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖)
              + ‖((x * ξ : ℝ) : ℂ) * Complex.I‖ := by gcongr; exact norm_sub_le _ _
          _ = 1 + 1 + |x * ξ| := by rw [Complex.norm_exp_ofReal_mul_I, hw]; simp
      have h2 : 1 + 1 + |x * ξ| ≤ 3 * (x * ξ) ^ 2 := by
        rw [← sq_abs (x * ξ)]; nlinarith
      nlinarith [sq_nonneg x, sq_nonneg R]
  · have hx2 : 1 ≤ x ^ 2 := by
      rw [not_lt] at h; nlinarith [sq_abs x]
    rw [min_eq_left hx2]
    simp only [h, if_false, mul_zero, sub_zero, mul_one]
    calc _ ≤ ‖Complex.exp ((x : ℂ) * ↑ξ * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        have : (x : ℂ) * ↑ξ * Complex.I = ((x * ξ : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]; norm_num
      _ ≤ _ := by nlinarith [sq_nonneg R]

theorem solution (ν : Measure ℝ)
    (hν : LevyFoundations.isLevyMeasure ν) (ξ : ℝ) :
    Integrable (LevyFoundations.compensatedIntegrand ξ) ν := by
  have hI : Integrable (fun x : ℝ => min 1 (x ^ 2)) ν := by
    refine ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
    exact hν.2
  have hmeas : Measurable (LevyFoundations.compensatedIntegrand ξ) := by
    have hite : Measurable (fun x : ℝ => (if |x| < 1 then (1 : ℂ) else 0)) :=
      Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const measurable_const
    unfold LevyFoundations.compensatedIntegrand
    exact (((Complex.measurable_ofReal.mul_const _).mul_const _).cexp.sub_const 1).sub
      (((Complex.measurable_ofReal.mul_const _).mul_const _).mul hite)
  exact (hI.const_mul (3 * |ξ| ^ 2 + 2)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => cad_bound ξ x |ξ| le_rfl)
