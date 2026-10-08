-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_nat_horizons
-- name    : AvramDividend.Classical.paymentTimes_eq_iUnion_nat_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:21:07.326973+00:00
-- url     : https://prove2.me/theorems/77691e31-45e9-4fab-b6be-80c2ddfd5479
-- title:
--   Payment times up to ruin are exhausted by deterministic integer horizons
-- statement:
--   For every extended nonnegative ruin time σ, the dividend-payment set [0,σ) together with the time-zero lump sum is the increasing union of the same payment set stopped at deterministic integer horizons n. This is the set-exhaustion step used when applying monotone convergence to pass from finite-horizon verification inequalities to the full dividend value.
-- source:
--   Deterministic set-theoretic component of the monotone-convergence passage following equation (5.13) in Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_eq_iUnion_nat_horizons
    (σ : ℝ≥0∞) :
    paymentTimes σ =
      ⋃ n : ℕ, paymentTimes (min σ (n : ℝ≥0∞)) := by sorry
