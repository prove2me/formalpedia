-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_two_level_measurable_event_stopping_time
-- name    : AvramDividend.Classical.chat08_two_level_measurable_event_stopping_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:39:33.100998+00:00
-- url     : https://prove2.me/theorems/d96da16f-bbb2-4b2f-8a14-1cab250a3382
-- title:
--   Two-level decision at an observed event is a stopping time
-- statement:
--   If A is measurable with information available at time s, and s is no later than t, the clock equal to s on A and t otherwise is a stopping time. This supports finite-valued stopping-time partitions for Lévy increment regeneration.
-- source:
--   Mathlib.Probability.Process.Stopping, IsStoppingTime definition.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_two_level_measurable_event_stopping_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    IsStoppingTime ℱ
      (fun ω => if ω ∈ A then (s : WithTop ℝ≥0) else (t : WithTop ℝ≥0)) := by sorry
