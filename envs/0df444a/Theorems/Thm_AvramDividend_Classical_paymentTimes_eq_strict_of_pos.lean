-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos
-- name    : AvramDividend.Classical.paymentTimes_eq_strict_of_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T21:10:27.427682+00:00
-- url     : https://prove2.me/theorems/7c01995b-bd0b-43b0-bb5e-3a05fb37de5b
-- title:
--   Positive reflected ruin times use precisely the strict stopped-payment interval
-- statement:
--   For every strictly positive extended nonnegative ruin time τ, the original prescribed paymentTimes set coincides exactly with nonnegative real times whose ENNReal.ofReal embedding is strictly below τ. The definition's additional time-zero convention becomes redundant because zero is already strictly before any positive τ. This isolates the genuinely special τ=0 case, whose original stopped dividend reward was separately remotely proved to vanish for the actual running-supremum measure.
-- source:
--   Actual paymentTimes definition in Definitions.Def_AvramDividend_Classical_ReflectionBarrier; accepted runningSup_reward_zero_at_instant_ruin 70673551-84b3-4b77-8b4d-0eb258cd9b8a motivates endpoint case.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_eq_strict_of_pos
    (τ : ℝ≥0∞) (hτ : 0 < τ) :
    paymentTimes τ = {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < τ} := by sorry
