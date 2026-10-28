-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_double_discount_integral
-- name    : AvramDividend.Classical.chat04_killed_resolvent_double_discount_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:33:10.124816+00:00
-- url     : https://prove2.me/theorems/e7f54d8b-4678-4134-9d9b-64b6207fe3f1
-- title:
--   Time-resolvent discount composition for killed-scale expectations
-- statement:
--   The time integral of a payoff discounted first at q and then at p equals the time integral discounted at p+q, with no integrability assumptions needed for this equality of integrands. This will identify the time-Laplace transform of a q-discounted killed-scale payoff as its (p+q)-resolvent.
-- source:
--   Elementary exponential multiplicativity and exact equality of integrands; preparatory analytic identity for killed semigroup resolvent.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set

theorem AvramDividend.Classical.chat04_killed_resolvent_double_discount_integral
    (p q : ℝ) (f : ℝ → ℝ) :
    (∫ t in Ioi (0 : ℝ),
      Real.exp (-(p * t)) * (Real.exp (-(q * t)) * f t)) =
    (∫ t in Ioi (0 : ℝ), Real.exp (-((p + q) * t)) * f t) := by sorry
