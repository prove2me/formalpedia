-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
-- name    : AvramDividend.Classical.stoppedHistory_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:31:08.159206+00:00
-- url     : https://prove2.me/theorems/8cb68dcc-7e7a-41f9-848f-b28effb5348a
-- title:
--   Stopped-past events for finite Lévy stopping times are globally measurable
-- statement:
--   For any finite-valued nonnegative stopping time τ, if A∩{τ≤s} is measurable in the history filtration at every fixed s, then A is measurable in the ambient sample space. This is needed to define the stopped-event indicator law and to use dominated-convergence limits without imposing a fixed stopping-time horizon.
-- source:
--   Unbounded stopped-history measurability prerequisite of general strong-Markov path-product theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8, which advances the W-free barrier-dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stoppedHistory_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    MeasurableSet A := by
  sorry
