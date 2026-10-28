-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedHistory_compl_event_adapted
-- name    : AvramDividend.Classical.stoppedHistory_compl_event_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:53:45.291677+00:00
-- url     : https://prove2.me/theorems/14adf425-f38f-4621-b8d2-fdc1e495b583
-- title:
--   The complement of a stopped-history event is a stopped-history event
-- statement:
--   The stopped-time sigma algebra is closed under complements: when τ is a finite stopping time and A is measurable in the stopped history, the complementary event Aᶜ is also measurable in the stopped history.
-- source:
--   Necessary complement-event case for constructing the stopped-path strong-Markov joint product law 61930a38-11f1-449e-bbb6-67d59c6d5ca8 from restricted future path laws, downstream of barrier split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.stoppedHistory_compl_event_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (Aᶜ ∩ {ω : Ω | τ ω ≤ s}) := by
  sorry
