-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_expected_dividend_budget_of_HJB_gradient_and_step_generator
-- name    : AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_HJB_gradient_and_step_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:41:59.770119+00:00
-- url     : https://prove2.me/theorems/43b2c10d-e40b-45f4-bd6d-3a16da8c91ed
-- title:
--   Expected discounted dividend bound from HJB gradient and one-step generator inequalities
-- statement:
--   For a finite-grid dividend strategy with nonnegative cash payments and a state update subtracting each payment from the pre-dividend reserve, impose w'≥1 on every payment interval. The mean-value theorem proves the pathwise jump-secant bound. Assume the uncontrolled Lévy residual at each grid step is integrable with nonpositive expectation and that the discounted terminal value is nonnegative in expectation. The previously certified stochastic expectation budget then yields the finite-horizon dividend bound. This theorem packages the discrete HJB verification implication, leaving continuous-time Lévy-Itô estimates and localisation for the canonical BV and UBV cores.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), HJB stochastic dividend verification.

import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_expected_dividend_budget_of_stepwise_levy_bound
import Theorems.Thm_AvramDividend_Classical_dividend_jump_drop_le_verification_drop_of_gradient

open MeasureTheory Finset Set
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_HJB_gradient_and_step_generator
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (u preDividend cash : ℕ → Ω → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0) (x : ℝ)
    (hu0 : ∀ ω, u 0 ω = x)
    (hAfter : ∀ k ω, u (k + 1) ω = preDividend k ω - cash k ω)
    (hCashNonneg : ∀ k ω, 0 ≤ cash k ω)
    (hwCont : ∀ k ω, ContinuousOn w
      (Icc (preDividend k ω - cash k ω) (preDividend k ω)))
    (hwDiff : ∀ k ω, DifferentiableOn ℝ w
      (interior (Icc (preDividend k ω - cash k ω) (preDividend k ω))))
    (hwGrad : ∀ k ω, ∀ y ∈
      interior (Icc (preDividend k ω - cash k ω) (preDividend k ω)),
        1 ≤ deriv w y)
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
