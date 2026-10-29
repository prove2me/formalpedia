-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_restricted_lintegral_factor_conditional
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_restricted_lintegral_factor_conditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:42:10.880783+00:00
-- url     : https://prove2.me/theorems/2ab4f429-ccea-439b-a0fa-1c8ece0cd37b
-- title:
--   Restricted event Laplace factorisation gives equality of conditional ENNReal expectations
-- statement:
--   If a finite measure P and a positive-mass measurable event A satisfy ∫_A f dP=P(A)∫ f dP for any extended-nonnegative measurable reward f, then the expectation of f under the normalised conditional measure P[|A] equals its unconditioned expectation. The result is exactly the normalisation needed to pass from the accepted Qp upper-ray Laplace factor theorem at each positive beta to the probability-law Laplace uniqueness route. Since all integrals and multipliers are in [0,infinity], no hidden finiteness assumption on the reward is needed; positivity and finiteness of the event mass justify cancellation.
-- source:
--   Pinned Mathlib ProbabilityTheory.cond (conditional measure), MeasureTheory.lintegral_smul_measure, ENNReal.inv_mul_cancel and finite measure_ne_top. No Wiener-Hopf or stochastic-process independence premise.

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Inv

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

theorem AvramDividend.Classical.avram_ws01e_bi_new_restricted_lintegral_factor_conditional
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hApos : P A ≠ 0)
    (f : Ω → ℝ≥0∞)
    (hFactor : (∫⁻ ω in A, f ω ∂P) = P A * (∫⁻ ω, f ω ∂P)) :
    (∫⁻ ω, f ω ∂(P[|A])) = ∫⁻ ω, f ω ∂P := by sorry
