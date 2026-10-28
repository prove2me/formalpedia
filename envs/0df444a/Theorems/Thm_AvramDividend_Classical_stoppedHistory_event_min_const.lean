-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_min_const
-- name    : AvramDividend.Classical.stoppedHistory_event_min_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:03:23.366546+00:00
-- url     : https://prove2.me/theorems/8ee1f437-c5b6-4e60-af95-4d69329e1b01
-- title:
--   Stopped-history event remains adapted after minimum-horizon truncation
-- statement:
--   If A is measurable at a finite stopping time τ, then A restricted to τ≤T is measurable at τ∧T. On a pre-horizon time s<T the stopped event reduces to A∩{τ≤s}; for T≤s it is A∩{τ≤T}. This permits localisation of the bounded-stopping strong-Markov reward theorem at arbitrary finite stopping times.
-- source:
--   Root-connected independent event truncation lemma for the no-scale-function strong-Markov stopped-path proof 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and subsequent dividend barrier split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.stoppedHistory_event_min_const
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T s : ℝ≥0) :
    MeasurableSet[𝓕 s]
      ((A ∩ {ω : Ω | τ ω ≤ T}) ∩
        {ω : Ω | min (τ ω) T ≤ s}) := by
  sorry
