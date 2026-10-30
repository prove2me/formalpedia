-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_positive_time_rational_prefix_exhaustion
-- name    : AvramDividend.Classical.avram_root29_05_positive_time_rational_prefix_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:42:19.494356+00:00
-- url     : https://prove2.me/theorems/6d37073b-69ae-456f-a0ed-1f5f758eb963
-- title:
--   Positive-time nonnegative Stieltjes reward is supremum of uniformly rational finite prefix integrals
-- statement:
--   For any measure on continuous real payment times and any nonnegative integrand, the full integral over strictly positive times equals the supremum of integrals over half-open intervals from zero to N/(n+1), for any fixed positive denominator n+1. This is genuine countable directed monotone convergence, with no finiteness assumption and correct treatment of time zero. It converts a fixed-grid finite-prefix actual regulator identity into the global integral needed for the Fatou reverse inequality.
-- source:
--   Pinned Mathlib setLIntegral_iUnion_of_directed, iUnion_Ioc_eq_Ioi_self_iff, exists_nat_ge, positive denominators and set interval-directedness. Supports source-level continuous stopped dividend valuation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.Positivity

open MeasureTheory Set
open scoped ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_positive_time_rational_prefix_exhaustion
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (n : ℕ) :
    (∫⁻ r in Ioi (0 : ℝ), f r ∂μ) =
      ⨆ N : ℕ, (∫⁻ r in Ioc (0 : ℝ)
        ((N : ℝ) / ((n : ℝ) + 1)), f r ∂μ) := by sorry
