-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_negative_quadratic_remainder
-- name    : AvramDividend.Classical.exp_negative_quadratic_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:24:56.158522+00:00
-- url     : https://prove2.me/theorems/c1906d86-131a-42b6-9753-7932a1b92219
-- title:
--   Global quadratic exponential remainder for nonpositive arguments
-- statement:
--   For every real t≤0, |exp(t)-1-t|≤t². For −1≤t≤0 this is the standard Mathlib Taylor remainder estimate for |t|≤1. For t≤−1, convexity gives exp(t)−1−t≥0, monotonicity gives exp(t)≤1 and t≤−1 implies −t≤t². This global one-sided bound avoids any smallness assumption and permits a uniform estimate on compensated negative-jump exponential Lévy kernels.
-- source:
--   Elementary global Taylor remainder bound, used for integrability of the Lévy–Khintchine exponential compensation.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem exp_negative_quadratic_remainder
    (t : ℝ) (ht : t ≤ 0) :
    ‖Real.exp t - 1 - t‖ ≤ t ^ 2 := by sorry
end AvramDividend.Classical
