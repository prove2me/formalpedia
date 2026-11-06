-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_terminal_vanish_of_uniform_integrable_payoff
-- name    : AvramDividend.Classical.avram_limit2_terminal_vanish_of_uniform_integrable_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:04:56.857595+00:00
-- url     : https://prove2.me/theorems/56d714ef-ab16-4f1e-bb4a-1b0124b1f4e5
-- title:
--   Vanishing discounted terminal expectations under uniform integrable payoff budgets
-- statement:
--   Uniform expected payoff bound and zero deterministic scale imply terminal expectation tends to zero, with finite M.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_terminal_vanish_of_uniform_integrable_payoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scale : ℕ → ℝ≥0∞) (Payoff Terminal : ℕ → Ω → ℝ≥0∞)
    (hPayoff : ∀ n, Measurable (Payoff n))
    (hBound : ∀ n ω, Terminal n ω ≤ scale n * Payoff n ω)
    (M : ℝ≥0∞) (hUniform : ∀ n, (∫⁻ ω, Payoff n ω ∂P) ≤ M)
    (hFinite : M ≠ ⊤)
    (hScale : Filter.Tendsto scale Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto (fun n => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
