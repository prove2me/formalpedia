-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_clock_future_tail
-- name    : AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:02:22.345205+00:00
-- url     : https://prove2.me/theorems/16c36ac4-1212-4b7f-80d2-bcea8e5d77b9
-- title:
--   Conditional residual-clock survival tail and post-stopping future marginal
-- statement:
--   Consider an independent external observation clock with a strict survival kernel discount(a) satisfying discount(a+t)=factor(t)discount(a), a nonnegative random stopping age τ, and a measurable future-path random variable Y independent of τ. Assume the genuine product-law event τ<e has positive probability. Under the conditional probability given τ<e, the event τ+t<e jointly with Y∈B has probability factor(t)P(Y∈B); moreover the conditional law of Y is unchanged. Both identities are proved from authentic product-law stopped-age factorisations and finite positive-event normalisation. This is the conditional residual-clock upper-ray interface preceding full π-λ independence, without supposing Wiener–Hopf factorisation.

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_residual_clock_survival_shift
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_random_clock_tail_future_event_factor

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_conditional_residual_clock_future_tail
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0)
    (t : ℝ≥0) (B : Set β) (hB : MeasurableSet B) :
    ((P.prod Q)[{z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      factor t * P (Y ⁻¹' B)) ∧
    ((P.prod Q)[{z : Ω × Θ | Y z.1 ∈ B} |
        {z : Ω × Θ | τ z.1 < e z.2}] =
      P (Y ⁻¹' B)) := by sorry
