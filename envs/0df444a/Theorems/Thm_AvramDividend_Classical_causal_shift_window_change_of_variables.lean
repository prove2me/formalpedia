-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_shift_window_change_of_variables
-- name    : AvramDividend.Classical.causal_shift_window_change_of_variables
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:09:14.57747+00:00
-- url     : https://prove2.me/theorems/aaf5a224-65fe-4047-bf2a-494abf18388a
-- title:
--   Translation of a causal integration window
-- statement:
--   If u≤x, the integral of g(t-u) on (u,x] is the integral of g on (0,x-u]. This is the interval-integral translation identity; it holds for arbitrary real-valued g because the Bochner integral is translation invariant.
-- source:
--   Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic, intervalIntegral.integral_comp_sub_right.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_shift_window_change_of_variables
    (g : ℝ → ℝ) (u x : ℝ) (hux : u ≤ x) :
    (∫ t in Ioc u x, g (t - u) ∂volume) =
    (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) := by sorry
