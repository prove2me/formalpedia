-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_translated_iff_shifted_of_pos
-- name    : AvramDividend.Classical.paymentTimes_translated_iff_shifted_of_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:20:39.261778+00:00
-- url     : https://prove2.me/theorems/309b576b-b728-4d10-9fb0-93e8d86286e3
-- title:
--   Positive relative payment times translate across a finite stopping-time origin
-- statement:
--   For finite nonnegative shift u, extended nonnegative ruin clock rho and positive relative t, absolute time u+t is in paymentTimes(u+rho) precisely when t is in paymentTimes(rho). Because paymentTimes has a special zero atom, t>0 is essential. The result uses ENNReal.ofReal_add and cancellation of strict inequalities under addition by finite u.
-- source:
--   Pinned definition paymentTimes and Mathlib ENNReal.ofReal_add and ENNReal.add_lt_add_iff_left. Needed by barrier-valuation strong Markov time shift.

import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.paymentTimes_translated_iff_shifted_of_pos
    (u : ℝ≥0) (ρ : ℝ≥0∞) (t : ℝ) (ht : 0 < t) :
    (u : ℝ) + t ∈ paymentTimes ((u : ℝ≥0∞) + ρ) ↔
      t ∈ paymentTimes ρ := by sorry
