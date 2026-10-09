-- Prove2me | Theorems.Thm_AvramDividend_Classical_corrected_discounted_exit_expectation_le_one
-- name    : AvramDividend.Classical.corrected_discounted_exit_expectation_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:20:23.884054+00:00
-- url     : https://prove2.me/theorems/64f14b0c-46c0-43a5-9d5d-7d1085fe3ef1
-- title:
--   Corrected infinite-time exit payoff has discounted expectation at most one
-- statement:
--   For a probability measure and any extended nonnegative exit time τ, define the payoff as zero on τ=∞ and e^{-q τ.toReal} on finite exits, with q≥0. Its nonnegative expectation is at most one. This explicitly fixes the infinite-time convention that invalidated the retired two-sided-exit expectation on Prove2Me; no-exit paths contribute zero, not exp(0)=1. The result is a rigorous probability bound independent of the unproved exit identity itself.
-- source:
--   Corrected stopping-time discount convention for the Avram Dividend two-sided exit identity; basic exponential and lintegral monotonicity.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem corrected_discounted_exit_expectation_le_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 ≤ q) (τ : Ω → ℝ≥0∞) :
    (∫⁻ ω, (if τ ω = ⊤ then (0 : ℝ≥0∞) else
      ENNReal.ofReal (Real.exp (-(q * (τ ω).toReal)))) ∂P) ≤ 1 := by sorry

end AvramDividend.Classical
