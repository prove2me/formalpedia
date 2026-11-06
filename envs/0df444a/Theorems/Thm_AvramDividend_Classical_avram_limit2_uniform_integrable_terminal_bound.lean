-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_integrable_terminal_bound
-- name    : AvramDividend.Classical.avram_limit2_uniform_integrable_terminal_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:04:57.716645+00:00
-- url     : https://prove2.me/theorems/b115439e-0a52-4665-8aef-6061c05d12b0
-- title:
--   Uniform integrable original terminal payoff gives scaled expected bound
-- statement:
--   A nonnegative terminal payoff dominated pointwise by deterministic scale times a stochastic payoff whose expected value is uniformly bounded by M has expected terminal at most scale times M.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_uniform_integrable_terminal_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scale : ℕ → ℝ≥0∞) (Payoff Terminal : ℕ → Ω → ℝ≥0∞)
    (hPayoff : ∀ n, Measurable (Payoff n))
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Payoff n ω)
    (M : ℝ≥0∞) (hUniform : ∀ n, (∫⁻ ω, Payoff n ω ∂P) ≤ M) :
    ∀ n, (∫⁻ ω, Terminal n ω ∂P) ≤ scale n * M := by sorry
