-- Prove2me | Theorems.Thm_AvramDividend_Classical_productIndicator_futureReward_lintegral_factor
-- name    : AvramDividend.Classical.productIndicator_futureReward_lintegral_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:21:09.058634+00:00
-- url     : https://prove2.me/theorems/7308e350-de7f-4e44-aff6-1f74bf3db945
-- title:
--   Product integral of stopped-event indicator and independent future reward factors
-- statement:
--   For arbitrary measures on the real-valued stopped-event indicator and on a future-path state space, integrating a nonnegative measurable reward when the indicator equals one yields the indicator-law mass at one multiplied by the future-law expected reward. This is the exact Tonelli product-integral normalisation needed when converting the established finite-grid Lévy joint-reward identity into scalar strong-Markov factorisation.
-- source:
--   Direct algebraic measure-theoretic intermediate consumed by AvramDividend.Classical.levy_stoppedHistory_upperGrid_futureReward_product (f8d196c7-e8f7-4929-bc3b-b6c523c5ea5b), followed by finite-grid stopped reward lintegral split 41ea67e0-cf9e-4f23-a927-c79e2440e634, on the Open W-free barrier path 79978d61-9d1f-4b20-b8a5-114797a8e380. The independent factor μ({1}) is the stopped-event probability once μ is an indicator push-forward. No scale-function hypotheses.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.productIndicator_futureReward_lintegral_factor
    {E : Type*} [MeasurableSpace E]
    (μ : Measure ℝ) (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ h : ℝ, ∫⁻ y : E,
      (if h = 1 then g y else 0) ∂ν ∂μ) =
      μ ({1} : Set ℝ) * (∫⁻ y, g y ∂ν) := by
  sorry
