-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_dividend_jump_bound
-- name    : AvramDividend.Classical.exponential_dividend_jump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:40:50.736205+00:00
-- url     : https://prove2.me/theorems/03fe29ff-3170-4aae-9f4d-4d2a3415f7a8
-- title:
--   Paying a feasible lump-sum dividend decreases exponential reserve value by at least the payment
-- statement:
--   Under θ≥1 and the dividend admissibility constraint 0≤d≤x, the reduction in e^(θ reserve) after paying d is at least d. Apply the exponential lump-sum gap estimate with remaining reserve u=x−d≥0. It isolates the discrete cash payout verification inequality for admissible dividend jumps.
-- source:
--   Child exponential_dividend_lump_sum_gap; the algebraic dividend jump inequality for exponential verification candidates.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.exponential_dividend_jump_bound
    (θ x d : ℝ) (hθ : 1 ≤ θ) (hd : 0 ≤ d) (hcap : d ≤ x) :
    d ≤ Real.exp (θ * x) - Real.exp (θ * (x - d)) := by sorry
