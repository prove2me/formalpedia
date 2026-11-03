-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_discount_exp_leftLim_eq_rightLim_on_nnreal
-- name    : AvramDividend.Classical.avram_wave6_05_discount_exp_leftLim_eq_rightLim_on_nnreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:43:38.883261+00:00
-- url     : https://prove2.me/theorems/030caf8f-321b-4723-9871-6873bfac582c
-- title:
--   Exponential discount has identical left and right limits at every nonnegative physical time
-- statement:
--   The actual deterministic discount factor exp(-q t) is continuous on the ordered nonnegative time domain for every real q, so its left limit equals its right limit at each t, including the bottom time 0. This removes the discount singleton atom in the actual bounded-variation Stieltjes endpoint correction without making any smoothness or continuity assumption on the dividend strategy or post-payment reserve.
-- source:
--   The map t↦exp(-q*(t:ℝ)) is continuous, by continuity of the nonnegative-real coercion, multiplication, negation and real exponential. ContinuousWithinAt.leftLim_eq and ContinuousWithinAt.rightLim_eq apply to the same continuous function at a on Iic a and Ici a. Both limits equal the pointwise value, so they agree.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_discount_exp_leftLim_eq_rightLim_on_nnreal
    (q : ℝ) (a : ℝ≥0) :
    Function.leftLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) a =
      Function.rightLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) a := by sorry
