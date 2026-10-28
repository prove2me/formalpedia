-- Prove2me | Theorems.Thm_AvramDividend_Classical_strict_stopping_order_event_stoppedHistory
-- name    : AvramDividend.Classical.strict_stopping_order_event_stoppedHistory
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:14:34.35705+00:00
-- url     : https://prove2.me/theorems/dbafe726-8f7b-44a4-a817-7b94f4969a5b
-- title:
--   Strict order of two stopping times is observable at the first stopping time
-- statement:
--   For any two extended nonnegative stopping times τ and σ on a real-time filtration, whether τ occurs strictly before σ is known at time τ. The defining stopped-history condition is that for every finite horizon s, the event {τ<σ, τ≤s} belongs to the sigma-algebra at s. This is the exact event-adaptedness needed to apply finite-horizon strong Markov factorisation to a successful barrier upcrossing preceding raw ruin. A proof partitions according to rational intermediate times between τ and σ and handles τ=s separately, preserving zero-duration and strict-endpoint cases.
-- source:
--   Source-faithful stopping-time measurability prerequisite for the first-upcrossing strong-Markov decomposition of Avram, Palmowski and Pistorius (2007), Proposition 1, and direct barrier-value parent 79978d61-9d1f-4b20-b8a5-114797a8e380. This result treats strict ordering of stopping clocks, without assuming the reflected-dividend valuation or the two-sided exit formula.

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.strict_stopping_order_event_stoppedHistory
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ σ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕 τ)
    (hσ : IsStoppingTime 𝓕 σ)
    (s : ℝ≥0) :
    MeasurableSet[𝓕 s]
      ({ω : Ω | τ ω < σ ω} ∩
        {ω : Ω | τ ω ≤ (s : ℝ≥0∞)}) := by
  sorry
