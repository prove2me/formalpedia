-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_grid_expected_dividends_le_initial_of_terminal_nonneg
-- name    : AvramDividend.Classical.exponential_grid_expected_dividends_le_initial_of_terminal_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T17:10:14.986694+00:00
-- url     : https://prove2.me/theorems/2494f1ef-c421-4f47-af87-f452ce2e1669
-- title:
--   Finite-grid expected discounted dividends bounded by initial verification value
-- statement:
--   Suppose the exponential-discount conditional finite-grid dividend budget holds for a probability measure, the initial grid time is zero and the initial reserve equals a deterministic x almost surely. Suppose the discounted expected terminal candidate value is nonnegative. Then the sum of expected discounted dividend payments across the grid is bounded by w(x). Apply the already proved exponential-grid budget, identify the initial integral with w(x) by probability normalisation, then remove the nonnegative terminal term. This is the finite-grid counterpart of the stopped capped BV/UV verification inequality. Establishing the adapted one-step bounds for arbitrary admissible strategies and the limiting Stieltjes integral remains a separate root-connected obligation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_exponential_grid_expected_dividend_budget_of_conditional_steps

open MeasureTheory ProbabilityTheory

theorem AvramDividend.Classical.exponential_grid_expected_dividends_le_initial_of_terminal_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (u a : ℕ → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (s : ℕ → ℝ) (x : ℝ)
    (hs0 : s 0 = 0)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hCashI : ∀ k, Integrable (fun ω => Real.exp (-(q * s k)) * a k ω) P)
    (hVI : ∀ k, Integrable (fun ω => Real.exp (-(q * s k)) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + Real.exp (-(q * (s (k + 1) - s k))) *
        (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω ≤ w (u k ω))
    (n : ℕ)
    (hterminal : 0 ≤
      ∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P) :
    (∑ k ∈ Finset.range n,
      ∫ ω, Real.exp (-(q * s k)) * a k ω ∂P) ≤ w x := by sorry
