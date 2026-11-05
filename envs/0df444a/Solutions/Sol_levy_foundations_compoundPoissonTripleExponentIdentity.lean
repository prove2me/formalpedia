-- Prove2me | solution 1 for levy_foundations_compoundPoissonTripleExponentIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:28.544004+00:00
-- url     : https://prove2.me/submissions/06f2fa1d-bade-45db-8dd7-053de8a80fa6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

theorem solution
    (b : ℝ) (r : ℝ≥0) (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (hlevy : LevyFoundations.isLevyMeasure ((r : ℝ≥0∞) • ν'))
    (ξ : ℝ) :
    LevyFoundations.exponent
      (LevyFoundations.compoundPoissonTripleGivenLevyMeasure b r ν' hlevy) ξ =
      Complex.I * b * ξ + r * (charFun ν' ξ - 1) := by
  have hind : Measurable (fun x : ℝ => (if |x| < 1 then (1:ℂ) else 0)) :=
    Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const measurable_const
  have hi1 : Integrable (fun x : ℝ => Complex.exp (↑x * ↑ξ * Complex.I)) ν' := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    have := Complex.norm_exp_ofReal_mul_I (x * ξ)
    push_cast at this
    exact this.le
  have hi3 : Integrable (fun x : ℝ => (x : ℂ) * ξ * Complex.I * (if |x| < 1 then (1:ℂ) else 0)) ν' := by
    refine Integrable.of_bound (by fun_prop) (|ξ|) (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : |x| < 1
    · simp only [hx, if_true, mul_one, norm_mul, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs]
      have : |x| * |ξ| ≤ 1 * |ξ| := mul_le_mul_of_nonneg_right hx.le (abs_nonneg _)
      linarith
    · simp [hx]
  set m : ℝ := ∫ x in {x : ℝ | |x| < 1}, x ∂ν' with hm
  have hmeasS : MeasurableSet {x : ℝ | |x| < 1} := measurableSet_lt (by fun_prop) measurable_const
  have h3eq : ∀ x : ℝ, (x : ℂ) * ξ * Complex.I * (if |x| < 1 then (1:ℂ) else 0) =
      (((if |x| < 1 then x else 0 : ℝ)) : ℂ) * (ξ * Complex.I) := by
    intro x
    by_cases hx : |x| < 1 <;> simp [hx]; ring
  have hI3 : ∫ x : ℝ, (x : ℂ) * ξ * Complex.I * (if |x| < 1 then (1:ℂ) else 0) ∂ν' =
      (m : ℂ) * (ξ * Complex.I) := by
    simp_rw [h3eq]
    rw [integral_mul_const, integral_complex_ofReal]
    congr 2
    rw [hm, ← integral_indicator hmeasS]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : |x| < 1 <;> simp [hx]
  have hcomp : ∫ x : ℝ, LevyFoundations.compensatedIntegrand ξ x ∂ν' =
      charFun ν' ξ - 1 - (m : ℂ) * (ξ * Complex.I) := by
    unfold LevyFoundations.compensatedIntegrand
    have h12 : Integrable (fun x : ℝ => Complex.exp (↑x * ↑ξ * Complex.I) - 1) ν' :=
      hi1.sub (integrable_const _)
    rw [integral_sub h12 hi3, integral_sub hi1 (integrable_const _), hI3, charFun_apply_real]
    simp [mul_comm]
  have hdrift : ∫ x in {x : ℝ | |x| < 1}, x ∂((r : ℝ≥0∞) • ν') = (r : ℝ) * m := by
    rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
    simp [hm]
  have hint : ∫ x : ℝ, LevyFoundations.compensatedIntegrand ξ x ∂((r : ℝ≥0∞) • ν') =
      (r : ℂ) * (charFun ν' ξ - 1 - (m : ℂ) * (ξ * Complex.I)) := by
    rw [integral_smul_measure, ENNReal.coe_toReal, hcomp, Complex.real_smul]
  simp only [LevyFoundations.exponent, LevyFoundations.compoundPoissonTripleGivenLevyMeasure]
  rw [hint, hdrift]
  push_cast
  ring
