-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_measurable_detection_time_or_infinity_is_stopping
-- name    : AvramDividend.Classical.chat08_measurable_detection_time_or_infinity_is_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:29:44.664285+00:00
-- url     : https://prove2.me/theorems/2b4b983b-fbe1-42a7-a82e-b757fb1fc2ce
-- title:
--   Adapted detection at a deterministic time, otherwise infinity, is a stopping time
-- statement:
--   If a decision event is observable at deterministic time s, the clock that equals s on detection and infinity otherwise is a stopping time. This is the building block for upcrossing on observation grids without a right-continuous-filtration hypothesis.
-- source:
--   MeasureTheory.IsStoppingTime and Filtration.mono.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_measurable_detection_time_or_infinity_is_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    IsStoppingTime ℱ
      (fun ω => if ω ∈ A then (s : WithTop ℝ≥0) else ⊤) := by sorry
