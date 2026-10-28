-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_interval_reward_le_full_indicator
-- name    : AvramDividend.Classical.stopped_interval_reward_le_full_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:22:42.059547+00:00
-- url     : https://prove2.me/theorems/a6e25980-6d28-472a-9b7c-0aef0b420564
-- title:
--   Stopped interval reward is bounded by the complete payment indicator integral
-- statement:
--   For any measure on the real line and any measurable set of permitted payment times, the nonnegative exponentially discounted reward on the intersection with a time interval cannot exceed the full permitted payment reward. The result rewrites the restricted-measure integral as the full-space integral of its measurable indicator. It is the final measure-theoretic comparison needed to turn survived record-grid interval bounds into bounds against the genuine stopped dividend reward.
-- source:
--   Mathlib lintegral_mono and lintegral_indicator.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.stopped_interval_reward_le_full_indicator
    (μ : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (q a b : ℝ) :
    (∫⁻ t in S,
      if t ∈ Set.Ioc a b then
        ENNReal.ofReal (Real.exp (-(q * t))) else 0 ∂μ) ≤
    (∫⁻ t,
      if t ∈ S then ENNReal.ofReal (Real.exp (-(q * t))) else 0
      ∂μ) := by sorry
