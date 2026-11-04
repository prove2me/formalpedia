-- Prove2me | solution 1 for levy_foundations_exponentContinuous
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:27:58.326992+00:00
-- url     : https://prove2.me/submissions/c1c9e495-c85b-4851-b520-b835cac2200a

import Mathlib.Topology.Instances.Complex
import Definitions.Def_levy_foundations_exponent

open LevyFoundations

open MeasureTheory Filter Topology

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

theorem solution (T : LevyFoundations.LevyKhintchineTriple) :
    Continuous (LevyFoundations.exponent T) := by
  have hint : Continuous fun ξ : ℝ => ∫ x, compensatedIntegrand ξ x ∂T.levyMeasure := by
    rw [continuous_iff_continuousAt]
    intro ξ₀
    have hI : Integrable (fun x : ℝ => min 1 (x ^ 2)) T.levyMeasure := by
      refine ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
      exact T.levyMeasure_condition.2
    have hmeas : ∀ ξ : ℝ, Measurable (compensatedIntegrand ξ) := by
      intro ξ
      have hite : Measurable (fun x : ℝ => (if |x| < 1 then (1 : ℂ) else 0)) :=
        Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const measurable_const
      unfold compensatedIntegrand
      exact (((Complex.measurable_ofReal.mul_const _).mul_const _).cexp.sub_const 1).sub
        (((Complex.measurable_ofReal.mul_const _).mul_const _).mul hite)
    apply continuousAt_of_dominated (bound := fun x => (3 * (|ξ₀| + 1) ^ 2 + 2) * min 1 (x ^ 2))
    · exact Filter.Eventually.of_forall fun ξ => (hmeas ξ).aestronglyMeasurable
    · have : ∀ᶠ ξ in 𝓝 ξ₀, |ξ| < |ξ₀| + 1 :=
        continuous_abs.continuousAt.eventually (Iio_mem_nhds (by linarith))
      exact this.mono fun ξ hξ => Filter.Eventually.of_forall fun x => cad_bound ξ x _ hξ.le
    · exact hI.const_mul _
    · refine Filter.Eventually.of_forall fun x => Continuous.continuousAt ?_
      unfold compensatedIntegrand
      fun_prop
  have h2 : Continuous fun ξ : ℝ => (↑T.drift * ↑ξ * Complex.I
      - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2 : ℂ) := by fun_prop
  exact h2.add hint

