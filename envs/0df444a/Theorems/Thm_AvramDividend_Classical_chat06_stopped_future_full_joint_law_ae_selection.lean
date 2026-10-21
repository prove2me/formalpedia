-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_stopped_future_full_joint_law_ae_selection
-- name    : AvramDividend.Classical.chat06_stopped_future_full_joint_law_ae_selection
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:57:27.800988+00:00
-- url     : https://prove2.me/theorems/eb5b27c2-0797-48a7-9890-5245d49e6a68
-- title:
--   Joint law of a randomly selected independent future
-- statement:
--   A randomly indexed future random vector retains its entire law if each selection event is almost surely a measurable past event and each deterministic-index future is independent of the observed past.
-- source:
--   Chat 06 standalone Lean source with verified private remote pinned compiler elaboration; exact SHA and job in SUBMISSIONS.json, no official proof yet.

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_stopped_future_full_joint_law_ae_selection
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace A]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (past : ℕ → Ω → A) (future : ℕ → Ω → E)
    (hFuture : ∀ n, Measurable (future n))
    (hInd : ∀ n, IndepFun (past n) (future n) P)
    (μ : Measure E)
    (hLaw : ∀ n, HasLaw (future n) μ P)
    (hStop : ∀ n, ∃ S : Set A, MeasurableSet S ∧
      (fun ω : Ω => N ω = n) =ᵐ[P]
      (fun ω : Ω => past n ω ∈ S)) :
    HasLaw (fun ω => future (N ω) ω) μ P := by sorry
