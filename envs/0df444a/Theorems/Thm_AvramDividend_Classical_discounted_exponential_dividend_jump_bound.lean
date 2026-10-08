-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_exponential_dividend_jump_bound
-- name    : AvramDividend.Classical.discounted_exponential_dividend_jump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:39:45.912589+00:00
-- url     : https://prove2.me/theorems/89cc4192-d96f-4935-9ed1-bf027ad6332b
-- title:
--   Discounted feasible dividend payment is bounded by discounted exponential reserve decrease
-- statement:
--   Any feasible lump-sum dividend d≤u at time t, discounted by exp(−qt), has cash value bounded by the correspondingly discounted drop in exp(θu), provided θ≥1. This is a pointwise discounted cash-payment version of the accepted exponential dividend jump bound and holds for any real discount rate q because exp is positive.
-- source:
--   Proved exponential_dividend_jump_bound and Real.exp_pos.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.discounted_exponential_dividend_jump_bound
    (θ q u d : ℝ) (t : ℝ≥0)
    (hθ : 1 ≤ θ) (hd : 0 ≤ d) (hcap : d ≤ u) :
    Real.exp (-(q * (t : ℝ))) * d ≤
      Real.exp (-(q * (t : ℝ))) *
      (Real.exp (θ * u) - Real.exp (θ * (u - d))) := by sorry
