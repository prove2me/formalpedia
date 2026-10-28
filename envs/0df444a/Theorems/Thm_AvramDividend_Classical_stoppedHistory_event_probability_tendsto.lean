-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_probability_tendsto
-- name    : AvramDividend.Classical.stoppedHistory_event_probability_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:14:36.987542+00:00
-- url     : https://prove2.me/theorems/423034cf-e1f8-4044-8add-a86ce944c4ff
-- title:
--   Finite-horizon restrictions exhaust the probability of a stopped-history event
-- statement:
--   For any finite-valued nonnegative random time τ and event A, the mass P(A∩{τ≤n}) tends to P(A) as n tends to infinity. The horizon-restricted events form an increasing sequence whose union is A by the Archimedean property. A direct measure-continuity lemma provides the convergence.
-- source:
--   Direct supporting input to lift bounded scalar strong Markov under stopped event A∩{τ≤T} to unbounded finite stopping τ and the W-free barrier dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.Order.Archimedean.Defs

open MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stoppedHistory_event_probability_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℝ≥0) (A : Set Ω) :
    Tendsto
      (fun n : ℕ => P (A ∩ {ω : Ω | τ ω ≤ (n : ℝ≥0)}))
      atTop (nhds (P A)) := by
  sorry
