-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
-- name    : AvramDividend.Classical.paymentTimes_min_zero_eq_singleton_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T13:58:48.914364+00:00
-- url     : https://prove2.me/theorems/77cdd573-4256-4dbd-8c0a-e95881be40e6
-- title:
--   At zero horizon the stopped payment set contains exactly the time-zero atom
-- statement:
--   Truncation of an extended nonnegative ruin clock at zero retains exactly the payment time zero, including the initial dividend atom for any ruin clock. This isolates the boundary case from the strict positive-horizon stopped-payment identity.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_min_zero_eq_singleton_zero
    (σ : ℝ≥0∞) :
    paymentTimes (min σ (0 : ℝ≥0∞)) = ({0} : Set ℝ) := by sorry
