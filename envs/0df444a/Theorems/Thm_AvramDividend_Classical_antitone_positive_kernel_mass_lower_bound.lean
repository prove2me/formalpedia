-- Prove2me | Theorems.Thm_AvramDividend_Classical_antitone_positive_kernel_mass_lower_bound
-- name    : AvramDividend.Classical.antitone_positive_kernel_mass_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:14:05.544079+00:00
-- url     : https://prove2.me/theorems/5ed99404-eb34-41c6-84d2-c50d4a3665b3
-- title:
--   Pointwise bound for an antitone positive-time kernel by its integrated mass
-- statement:
--   For an integrable real kernel decreasing on positive times, the positive-time value K(x) multiplied by x cannot exceed the accumulated integral from zero to x. In particular this controls a decreasing causal kernel by its L1 mass divided by the positive time. No boundedness at the origin is required.
-- source:
--   Quantitative first step toward polynomial-geometric bounds on convolution powers of the decreasing Gaussian double-tail Volterra kernel.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Monotone.Defs

open MeasureTheory Set

theorem AvramDividend.Classical.antitone_positive_kernel_mass_lower_bound
    (K : ℝ → ℝ) (hanti : AntitoneOn K (Ioi (0 : ℝ)))
    (x : ℝ) (hx : 0 < x)
    (hint : IntervalIntegrable K volume 0 x) :
    x * K x ≤ ∫ t in (0 : ℝ)..x, K t := by sorry
