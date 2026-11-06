-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_discounted_terminal_vanish_of_uniform_expected_payoffs
-- name    : AvramDividend.Classical.avram_limit2_discounted_terminal_vanish_of_uniform_expected_payoffs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:07:00.872196+00:00
-- url     : https://prove2.me/theorems/d0605a55-016c-461e-9f6e-71c8d840a4cd
-- title:
--   Uniformly L1-bounded original stopped payoffs have vanishing positive-rate terminal expectation
-- statement:
--   A nonnegative random terminal reserve payoff discounted at any strictly positive rate has expected discounted terminal amount tending to zero when its undiscounted expected payoff is uniformly bounded over integer horizons by a finite value. This requires a genuine uniform expectation bound; it does not assert the Avram original reserve automatically satisfies it.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_discounted_terminal_vanish_of_uniform_expected_payoffs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ) (hq : 0 < q)
    (Payoff Terminal : ℕ → Ω → ℝ≥0∞)
    (hPayoff : ∀ n, Measurable (Payoff n))
    (hBound : ∀ n ω, Terminal n ω ≤
      ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))) * Payoff n ω)
    (M : ℝ≥0∞) (hUniform : ∀ n, (∫⁻ ω, Payoff n ω ∂P) ≤ M)
    (hFinite : M ≠ ⊤) :
    Filter.Tendsto (fun n => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
