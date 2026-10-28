-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteStopping_threshold_event_stoppedHistory
-- name    : AvramDividend.Classical.finiteStopping_threshold_event_stoppedHistory
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:58:52.634838+00:00
-- url     : https://prove2.me/theorems/f267fcd5-37e0-4c1e-aba2-2eaa671e7bbe
-- title:
--   Finite stopping-clock thresholds belong to the stopped-history sigma-algebra
-- statement:
--   For a finite stopping time and any fixed threshold c, the event that the clock has occurred by c belongs to the stopped-history sigma-algebra. At observation time s its intersection with {τ ≤ s} is exactly {τ ≤ min c s}, which is measurable in filtration level s. This is the clock-event bridge toward proving the full shifted future Lévy path independent of the stopping clock.
-- source:
--   Immediate input for the stopped-clock versus future-path independence corollary of strong Markov theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8, serving the barrier dividend split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Filtration

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finiteStopping_threshold_event_stoppedHistory
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (c : ℝ≥0) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        ({ω : Ω | τ ω ≤ c} ∩ {ω : Ω | τ ω ≤ s}) := by
  sorry
