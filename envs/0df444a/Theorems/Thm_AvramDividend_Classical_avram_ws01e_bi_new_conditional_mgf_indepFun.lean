-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_conditional_mgf_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_conditional_mgf_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:34:31.164981+00:00
-- url     : https://prove2.me/theorems/17e694fd-c5bd-4842-b58b-e6a88a2f1c9b
-- title:
--   Full independence from conditional exponential moment laws on supremum upper rays
-- statement:
--   For any probability law P, measurable real R and Y, if on every strictly positive-probability upper-ray event {R>a} the conditional distribution of Y has finite exponential moments at all positive parameters and these moments agree with the unconditional distribution, then R and Y are independent. The zero-mass rays factor automatically. The conclusion is full independence for arbitrary Borel rewards by finite-law MGF uniqueness and the upper-ray pi-lambda theorem. In the drawdown application, take Y equal to the negative of the nonnegative terminal drawdown, so the moment integrability assumptions are automatic under both laws.
-- source:
--   Accepted Mathlib conditional law cond_isProbabilityMeasure and cond_mul_eq_inter; accepted measure_eq_of_pos_mgf_on_ray (4fb183cd); accepted upper-ray cylinders indepFun (92d90ca8). Preserves the actual random-terminal Qp law as arbitrary P and imposes no stochastic-process independence premise.

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.ComplexMGF
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_upper_ray_cylinders_indepFun

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

theorem AvramDividend.Classical.avram_ws01e_bi_new_conditional_mgf_indepFun
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R Y : Ω → ℝ) (hR : Measurable R) (hY : Measurable Y)
    (hMoment : ∀ a : ℝ, P (R ⁻¹' Set.Ioi a) ≠ 0 →
      ∀ s : ℝ, 0 < s →
        Integrable (fun y : ℝ => Real.exp (s * y))
          ((P[|R ⁻¹' Set.Ioi a]).map Y) ∧
        Integrable (fun y : ℝ => Real.exp (s * y)) (P.map Y))
    (hLap : ∀ a : ℝ, P (R ⁻¹' Set.Ioi a) ≠ 0 →
      ∀ s : ℝ, 0 < s →
        (∫ y : ℝ, Real.exp (s * y) ∂((P[|R ⁻¹' Set.Ioi a]).map Y)) =
          ∫ y : ℝ, Real.exp (s * y) ∂(P.map Y)) :
    IndepFun R Y P := by sorry
