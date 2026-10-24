-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
-- name    : AvramDividend.Classical.paymentTimes_min_mono_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T13:59:50.232031+00:00
-- url     : https://prove2.me/theorems/021cfe05-e7e2-40b3-acd0-0850489ea100
-- title:
--   Stopped payment sets are monotone in the extended nonnegative horizon
-- statement:
--   For an extended nonnegative ruin clock and two horizons s ≤ t, every payment time selected by stopping at min(σ,s) is also selected at min(σ,t). This set inclusion is a deterministic monotonicity ingredient for monotone convergence of expected stopped Stieltjes dividend rewards and retains the time-zero atom.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_min_mono_horizon
    (σ s t : ℝ≥0∞) (hst : s ≤ t) :
    paymentTimes (min σ s) ⊆ paymentTimes (min σ t) := by sorry
