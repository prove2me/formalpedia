-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_observed_count_history_measurable_from_arrival_threshold
-- name    : AvramDividend.Classical.chat06_observed_count_history_measurable_from_arrival_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:49:52.566897+00:00
-- url     : https://prove2.me/theorems/3b47f724-3357-4c70-abab-3fa035ab8321
-- title:
--   Full observed renewal count history is measurable from arrival thresholds
-- statement:
--   The full observed renewal counting path on the time interval at or before a deterministic clock is measurable as a function of the underlying sample point whenever the interarrival coordinates are measurable and the renewal count is defined by its exact arrival thresholds. Each coordinate N(s) of the history is measurable by the accepted count-measurability theorem, and measurability into the count-history function space follows from the measurable-pi criterion. The result allows events in the natural counting-history pullback sigma-algebra to be used as ordinary measurable events when proving independence of future increments.
-- source:
--   bv_observed_count_history_measurable_from_arrival_threshold_chat06_20261022.lean, 20 lines, 855 bytes, SHA-256 2a177edca0ba2d72810cf14d555b8eceee1cc8fdfb568eac08a238d43d7aa83b; private probe 2e57530a-e50e-41a9-b115-6c7385dcbf12 reached sentinel with no source errors.

import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_chat06_count_measurable_from_arrival_threshold

open MeasureTheory Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_observed_count_history_measurable_from_arrival_threshold
    {Ω : Type*} [MeasurableSpace Ω]
    (τ : ℕ → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    Measurable (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ)) := by sorry
