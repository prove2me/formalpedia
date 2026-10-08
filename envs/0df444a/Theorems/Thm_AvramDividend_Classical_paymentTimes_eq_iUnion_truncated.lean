-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_truncated
-- name    : AvramDividend.Classical.paymentTimes_eq_iUnion_truncated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:04:29.774138+00:00
-- url     : https://prove2.me/theorems/aeb4c8b8-3c61-4af0-abe7-074b4ca345f0
-- title:
--   Payment times are exhausted by deterministic integer horizons
-- statement:
--   Every payment time is nonnegative and finite as a real time, so it lies below some natural-number horizon. Hence the full payment-time set is the increasing union of its intersections with (-infinity,n].
-- source:
--   Elementary set-theoretic exhaustion used in the monotone-convergence step for Proposition 4(i) of Avram-Palmowski-Pistorius.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_eq_iUnion_truncated
    (σ : ℝ≥0∞) :
    paymentTimes σ = ⋃ n : ℕ, paymentTimes σ ∩ Iic (n : ℝ) := by sorry
