-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_residual_clock_survival_shift
-- name    : AvramDividend.Classical.avram_ws01e_b_residual_clock_survival_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:09:16.053996+00:00
-- url     : https://prove2.me/theorems/b9bfc5be-69dc-40d0-936b-ba38728528d2
-- title:
--   Memoryless independent clock: random stopping-age plus time shift factors from shifted future event
-- statement:
--   Under a genuine independent observation clock with nonnegative random age τ, measurable future-path statistic Y independent of τ under P, and strict-survival kernel discount satisfying discount(a+t)=factor(t) discount(a), the joint probability of {τ+t<e, Y∈B} under P×Q equals factor(t) times the probability of {τ<e} times P(Y∈B), for all nonnegative t and measurable B. This is a genuine stopping-age residual-clock factor, without assuming Wiener–Hopf independence; in the exponential instance factor(t)=exp(-p t).
-- source:
--   Accepted AvramDividend.Classical.avram_ws01e_b_random_clock_tail_future_event_factor 48753cde-ea9d-4299-95c2-dbde801b80d7, MeasureTheory.Measure.prod_apply, MeasureTheory.lintegral_const_mul and exponential memorylessness; Kuznetsov–Kyprianou–Rivero (2012), section on Wiener–Hopf at exponential times.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_random_clock_tail_future_event_factor

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_residual_clock_survival_shift
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
    (hShift : ∀ a t : ℝ≥0,
      discount (a + t) = factor t * discount a)
    (t : ℝ≥0) (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q) {z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ B} =
      factor t * (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} *
        P (Y ⁻¹' B) := by sorry
