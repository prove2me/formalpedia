-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividend_weight_time_shift
-- name    : AvramDividend.Classical.discounted_dividend_weight_time_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:48:45.306259+00:00
-- url     : https://prove2.me/theorems/0b09e6d5-a563-4b2b-80c6-1b9e6fcef73f
-- title:
--   Discount factor multiplication under a stopping-time shift
-- statement:
--   The exponential discount factor at time u+t is the product of discount factors at u and t, including after embedding into ENNReal. This is the pathwise time-shift discount identity needed for the dividend Stieltjes integral in the strong-Markov barrier factorisation.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 1; Real.exp_add and ENNReal.ofReal_mul.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.discounted_dividend_weight_time_shift
    (q : ℝ) (u t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * ((u + t : ℝ≥0) : ℝ)))) =
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) := by sorry
