-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_expected_dividend_budget_of_levy_residual
-- name    : AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_levy_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:01:18.919156+00:00
-- url     : https://prove2.me/theorems/bd80896f-75c6-4584-a861-af382f20dcdd
-- title:
--   Expected stopped-grid dividend budget from nonpositive Lévy generator residual
-- statement:
--   A finite stochastic dividend grid has a pathwise secant inequality for payments and a possibly signed discounted Lévy residual. The accepted pathwise ledger, expectation monotonicity and integrability imply that expected discounted dividends are bounded by initial verification capital when the expected Lévy residual is nonpositive and the terminal expected verification value is nonnegative. This precisely isolates the conditional generator/Dynkin inequality needed for the stochastic BV and UBV verification cores while keeping the expected-dividend accounting rigorous.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), expected stopped discounted verification inequality.

import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_levy_dividend_secant_ledger

open MeasureTheory Finset
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_levy_residual
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
    (hResidualInt : Integrable (fun ω =>
      ∑ k ∈ Finset.range n,
        (Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
          Real.exp (-(q * s k)) * w (u k ω))) P)
    (hResidual : (∫ ω, ∑ k ∈ Finset.range n,
      (Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω)) ∂P) ≤ 0)
    (hTerminal : 0 ≤
      ∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P) :
    (∫ ω, ∑ k ∈ Finset.range n,
      Real.exp (-(q * s (k + 1))) * cash k ω ∂P) ≤ w x := by sorry
