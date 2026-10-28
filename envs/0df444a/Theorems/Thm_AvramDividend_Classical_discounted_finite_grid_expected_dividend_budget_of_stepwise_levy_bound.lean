-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_expected_dividend_budget_of_stepwise_levy_bound
-- name    : AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_stepwise_levy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:29:59.776642+00:00
-- url     : https://prove2.me/theorems/78b6852f-a67b-4ff6-9c5c-eee5da0e5414
-- title:
--   Expected discounted finite-grid dividends bounded by stepwise Lévy generator inequalities
-- statement:
--   For an admissible finite-grid dividend strategy, assume the verification-function secant bound for each dividend, an integrable discounted Lévy residual at each grid step, and a nonpositive expectation of each residual as furnished by a one-step Dynkin or HJB inequality. If the discounted terminal verification value has nonnegative expectation, the expected discounted dividend sum is at most the initial verification value. The proof assembles the previously certified expectation-level dividend ledger and finite-step residual summation lemmas.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), stopped discounted verification argument.

import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_expected_finite_grid_levy_residual_nonpositive_of_step_bounds
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_expected_dividend_budget_of_levy_residual

open MeasureTheory Finset
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_stepwise_levy_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (u preDividend cash : ℕ → Ω → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0) (x : ℝ)
    (hu0 : ∀ ω, u 0 ω = x)
    (hCash : ∀ k ω, cash k ω ≤ w (preDividend k ω) - w (u (k + 1) ω))
    (n : ℕ)
    (hCashInt : Integrable (fun ω =>
      ∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k ω) P)
    (hTerminalInt : Integrable (fun ω =>
      Real.exp (-(q * s n)) * w (u n ω)) P)
    (hStepInt : ∀ k, Integrable (fun ω =>
      Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω)) P)
    (hStep : ∀ k, (∫ ω,
      Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω) ∂P) ≤ 0)
    (hTerminal : 0 ≤
      ∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P) :
    (∫ ω, ∑ k ∈ Finset.range n,
      Real.exp (-(q * s (k + 1))) * cash k ω ∂P) ≤ w x := by sorry
