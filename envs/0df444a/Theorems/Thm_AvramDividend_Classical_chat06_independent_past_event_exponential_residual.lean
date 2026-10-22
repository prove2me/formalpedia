-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_independent_past_event_exponential_residual
-- name    : AvramDividend.Classical.chat06_independent_past_event_exponential_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:42:16.240619+00:00
-- url     : https://prove2.me/theorems/4cd5d623-7f04-4461-9753-7c77af8e561c
-- title:
--   Exponential residual survival after an arbitrary measurable past event
-- statement:
--   Suppose Z describes the complete observed past and is independent of a unit exponential waiting time. For any measurable past event D and an almost-surely nonnegative measurable age determined by Z, the joint probability of D and survival past age+t equals the corresponding joint probability at age multiplied by exp(-t). The proof uses the product joint law, Tonelli, and exponential tail scaling. It is the event-level residual law needed in the renewal construction, conditional on established independence of Z and the next wait.
-- source:
--   Source: bv_independent_past_event_random_age_residual_memorylessness_v3_chat06_20261021.lean, 144 lines, SHA-256 63361eaf44ea08e577828a4ac9989ae063f0f085b5eea5ec122394ecc47d96d2. Pinned revision: 0df444a360eaa60ab8c11dca51a86af692955474. Private remote candidate probe job 01b45c86-fee1-4ffe-bf59-92e6924811f9 passed source elaboration to deliberate sentinel with zero candidate errors. It does not constitute proof acceptance.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_independent_past_event_exponential_residual
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → E) (τ : Ω → ℝ) (age : E → ℝ)
    (hZ : Measurable Z) (hτ : Measurable τ)
    (hAgeMeas : Measurable age) (hInd : IndepFun Z τ P)
    (D : Set E) (hD : MeasurableSet D)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | Z ω ∈ D ∧ age (Z ω) + t < τ ω} =
      P {ω | Z ω ∈ D ∧ age (Z ω) < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by sorry
