-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_finite_nonnegative_interval_integral_le_positive_halfline
-- name    : AvramDividend.Classical.chat07_finite_nonnegative_interval_integral_le_positive_halfline
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:48:17.171817+00:00
-- url     : https://prove2.me/theorems/b4f61d04-de49-447c-a6db-52000ae644d4
-- title:
--   Finite nonnegative interval mass bounded by positive-halfline mass
-- statement:
--   For a real-valued function g that is Lebesgue integrable over (0,∞) and nonnegative on the real line, its integral on [1,n+1] is bounded by its integral over (0,∞) for every natural n. This is the set-integral comparison needed to turn finite telescoped adjacent-unit inequalities into a uniform bound for the weighted scale derivative.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.chat07_finite_nonnegative_interval_integral_le_positive_halfline
    (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi (0 : ℝ)))
    (hgnonneg : ∀ x : ℝ, 0 ≤ g x) (n : ℕ) :
    (∫ x in (1 : ℝ)..((n : ℝ) + 1), g x) ≤
      (∫ x in Ioi (0 : ℝ), g x) := by sorry
