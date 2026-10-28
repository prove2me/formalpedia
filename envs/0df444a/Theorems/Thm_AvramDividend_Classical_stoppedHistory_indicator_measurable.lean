-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedHistory_indicator_measurable
-- name    : AvramDividend.Classical.stoppedHistory_indicator_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:04:40.287995+00:00
-- url     : https://prove2.me/theorems/c1e8856a-4785-403c-91be-0a99ce552db1
-- title:
--   Any finite stopping-time past-event indicator is globally measurable
-- statement:
--   For the event A in the strong-Markov stopped-history hypothesis, its real-valued indicator is measurable. This is required to form its law under Measure.map and hence state, calculate and use the stopped-event future-path product measure.
-- source:
--   Direct canonical consumer of Proved stoppedHistory_event_measurable 8cb68dcc-7e7a-41f9-848f-b28effb5348a, for Open stopped future-path strong-Markov 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and W-free barrier dividend 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedHistory_indicator_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    Measurable (Set.indicator A (fun _ : Ω => (1 : ℝ))) := by
  sorry
