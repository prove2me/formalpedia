-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_iff_negative_times_after_horizon
-- name    : AvramDividend.Classical.chat04_closed_survival_iff_negative_times_after_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:21:55.485889+00:00
-- url     : https://prove2.me/theorems/9fe2380f-2900-4f65-9093-c38e9b0165a8
-- title:
--   Survival through a horizon iff all negative times occur afterwards
-- statement:
--   For an arbitrary real reserve path indexed by nonnegative times, surviving at every time up to and including t is equivalent to every strictly negative reserve occurring at a time strictly later than t. This exact event equivalence handles the endpoint and is a bridge to first-passage conventions without requiring a set infimum expression.
-- source:
--   Elementary order reasoning, valid for all paths without regularity or stochastic assumptions.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem AvramDividend.Classical.chat04_closed_survival_iff_negative_times_after_horizon
    (f : NNReal → ℝ) (t : NNReal) :
    (∀ s : NNReal, s ≤ t → 0 ≤ f s) ↔
      ∀ s : NNReal, f s < 0 → t < s := by sorry
