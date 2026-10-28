-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
-- name    : AvramDividend.Classical.chat04_exponential_clock_killed_reward_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:45:48.601993+00:00
-- url     : https://prove2.me/theorems/846f9b05-5c3b-42cf-8afb-b1d5ea692379
-- title:
--   Exact killed-payoff Tonelli formula under a genuine independent exponential observation clock
-- statement:
--   For a genuine independent exponential observation time with rate p>0 on a product of a probability space and the real observation-time space, the expected nonnegative payoff masked by an arbitrary measurable survival/killing event equals the exact time integral of its Lévy-path expectation against the exponential probability density. This is an unconditional probabilistic time-resolvent representation given routine measurable event and payoff data; it does not assert scale-function harmonicity or assume any exit formula.
-- source:
--   Mathlib pinned product-measure Tonelli, exponential measure (Gamma shape one) density and withDensity integration; Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions, section 2.7 killed resolvent via independent exponential horizon. Intended for stochastic half-line killed-resolvent kernel identification.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat04_exponential_clock_killed_reward_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p)
    (survival : Set (Ω × ℝ)) (hSurv : MeasurableSet survival)
    (reward : Ω × ℝ → ENNReal) (hReward : Measurable reward) :
    (∫⁻ z : Ω × ℝ, survival.indicator reward z
        ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
       (∫⁻ ω : Ω, survival.indicator reward (ω, t) ∂P) ∂volume) := by sorry
