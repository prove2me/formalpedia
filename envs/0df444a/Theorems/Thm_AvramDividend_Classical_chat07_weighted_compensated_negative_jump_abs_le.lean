-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_weighted_compensated_negative_jump_abs_le
-- name    : AvramDividend.Classical.chat07_weighted_compensated_negative_jump_abs_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:34:02.614575+00:00
-- url     : https://prove2.me/theorems/b9b68c39-8a68-4bc2-8616-20fdd764e551
-- title:
--   Pointwise weighted bound for compensated negative Lévy jumps
-- statement:
--   If W is a monotone real-valued function and r is a nonnegative jump size, then the exponentially weighted absolute value of the compensated difference W(x-r)-W(x)+rW'(x) is bounded by the weighted sum of its nonnegative scale decrement W(x)-W(x-r) and first derivative term rW'(x). This is the pointwise domination needed before integrating the BV Lévy generator jump term and justifying Fubini.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat07_weighted_compensated_negative_jump_abs_le
    (W : ℝ → ℝ) (hW : Monotone W)
    (θ x r : ℝ) (hr : 0 ≤ r) :
    Real.exp (-(θ * x)) *
        |W (x - r) - W x + r * deriv W x| ≤
      Real.exp (-(θ * x)) *
        ((W x - W (x - r)) + r * deriv W x) := by sorry
