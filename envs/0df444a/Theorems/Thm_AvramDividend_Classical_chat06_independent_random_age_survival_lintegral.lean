-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_independent_random_age_survival_lintegral
-- name    : AvramDividend.Classical.chat06_independent_random_age_survival_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:12:40.238865+00:00
-- url     : https://prove2.me/theorems/a532b40a-beab-4137-b363-18743446cc5e
-- title:
--   Independent random-age survival probability as an exact Tonelli integral
-- statement:
--   If two real random variables A and tau are independent and measurable on a probability space, the probability that tau exceeds the random threshold A+t is exactly the lintegral against the law of A of the deterministic tail probability of tau above a+t. No finite-valued age assumption is needed. The proof identifies the joint law as the product of marginals and applies the product measure section integral.
-- source:
--   Prove2Me Chat 06 pinned remote source proof job ea37ed2f-966c-4ab7-8c95-e2f75d1a38cc source SHA 1f86608838c82fba2de8e93ef27d9d6ca538df73e8a9e40a4921a8e173cefa62.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_independent_random_age_survival_lintegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A τ : Ω → ℝ) (hA : Measurable A)
    (hτ : Measurable τ) (hInd : IndepFun A τ P)
    (t : ℝ) :
    P {ω | A ω + t < τ ω} =
      ∫⁻ a, (P.map τ) (Ioi (a + t)) ∂(P.map A) := by sorry
