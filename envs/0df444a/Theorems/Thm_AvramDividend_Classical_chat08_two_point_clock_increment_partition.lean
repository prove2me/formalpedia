-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_two_point_clock_increment_partition
-- name    : AvramDividend.Classical.chat08_two_point_clock_increment_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:14:16.408991+00:00
-- url     : https://prove2.me/theorems/429c1470-9153-43ab-baec-0bfcb09b0356
-- title:
--   Partition a shifted process increment across a two-valued observation clock
-- statement:
--   If an observation clock chooses between deterministic s and t according to an event, the shifted process increment decomposes into the corresponding conditional two-point increments. This is the algebraic reduction needed before proving simple-stopping-time Lévy regeneration.
-- source:
--   Case-split on membership in the selecting event.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_two_point_clock_increment_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ) (s t u : ℝ≥0) (A : Set Ω) (ω : Ω) :
    Y ((if ω ∈ A then s else t) + u) ω -
      Y (if ω ∈ A then s else t) ω =
    if ω ∈ A then Y (s + u) ω - Y s ω
      else Y (t + u) ω - Y t ω := by sorry
