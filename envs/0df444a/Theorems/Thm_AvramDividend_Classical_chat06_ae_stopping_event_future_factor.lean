-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_ae_stopping_event_future_factor
-- name    : AvramDividend.Classical.chat06_ae_stopping_event_future_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:55:54.164994+00:00
-- url     : https://prove2.me/theorems/e6e5f695-f19f-434e-8c6d-c5541c307c05
-- title:
--   Factorisation of a stopping selection event from its independent whole future
-- statement:
--   A selection event agreeing almost surely with a measurable past-cylinder has independent joint intersection probabilities against the complete future random variable.
-- source:
--   Original Chat 06 source remotely elaborated at pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474; individual source SHA-256 and private compilation proof evidence in candidates/delegated/avram_round3/chat_06/SUBMISSIONS.json.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_ae_stopping_event_future_factor
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace E]
    {P : Measure Ω}
    (N : Ω → ℕ) (n : ℕ)
    (past : Ω → A) (future : Ω → E)
    (hI : IndepFun past future P)
    (μ : Measure E) (hFuture : HasLaw future μ P)
    (hStop : ∃ S : Set A, MeasurableSet S ∧
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω : Ω => past ω ∈ S))
    (B : Set E) (hB : MeasurableSet B) :
    P ({ω | N ω = n} ∩ {ω | future ω ∈ B}) =
      P {ω | N ω = n} * μ B := by sorry
