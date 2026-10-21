-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_weight_le_one
-- name    : AvramDividend.Classical.chat03_discounted_upperfirst_weight_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:21:53.255883+00:00
-- url     : https://prove2.me/theorems/ca2f713b-22b7-4816-94d2-120e3e3a1147
-- title:
--   The exact two-sided upper-first discount reward is at most one
-- statement:
--   For every nonnegative real discount rate q and arbitrary extended nonnegative upper and lower passage clocks, the exact upper-first weight (if up<down then ofReal(exp(-q*toReal up)) else zero) is bounded above by one. The bound holds even for infinite clock values because ENNReal.toReal is nonnegative. On the upper-first event, the exponential is at most one, and otherwise the weight is zero. This is the uniform deterministic domination needed for bounded convergence and finiteness of the exact parent stopped-scale exit integral.
-- source:
--   Pinned Mathlib Real.exp_le_one_iff, ENNReal.ofReal_le_one and ENNReal.toReal_nonneg.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Basic

open scoped ENNReal

theorem AvramDividend.Classical.chat03_discounted_upperfirst_weight_le_one
    (q : ℝ) (hq : 0 ≤ q) (up down : ℝ≥0∞) :
    (if up < down then
       ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
     else 0) ≤ 1 := by sorry
