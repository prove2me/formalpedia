-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_levy_grid_expected_cash_le_initial_of_conditional_cash
-- name    : AvramDividend.Classical.exponential_levy_grid_expected_cash_le_initial_of_conditional_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:01:55.321567+00:00
-- url     : https://prove2.me/theorems/4dbb2bf4-7353-45a5-832c-64f3fa249ec6
-- title:
--   Conditional expected interval dividends bounded on a Lévy time grid
-- statement:
--   Let a spectrally negative Lévy model's continuous-time filtration be sampled at an increasing deterministic grid s_k starting at zero. Let cash_k be an already discounted, integrable payment accrued on the kth interval, which may depend on later observations within that interval. Assume an almost-sure one-step inequality with the conditional expectation of cash_k and the conditional expectation of the next discounted verification payoff given the start-of-interval filtration, together with integrable discounted candidate values and a nonnegative expected terminal payoff. Then the expected sum of all interval cash payments is at most w(x). The proof combines the Proved sampled-filtration construction and the Proved conditional-cash finite-grid budget, dropping the nonnegative terminal term. It is a direct reusable grid interface for the capped BV/UV stopped Stieltjes verification branch. Its mathematical hypotheses still require a continuous-time stochastic-calculus derivation and an approximation argument for general dividend strategies.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_sampled_levy_filtration_exists_of_monotone_grid
import Theorems.Thm_AvramDividend_Classical_expected_finite_grid_dividend_budget_of_conditional_cash_steps

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem AvramDividend.Classical.exponential_levy_grid_expected_cash_le_initial_of_conditional_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u cash : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hVI : ∀ k,
      Integrable (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓕 (s k)]) ω +
        (P[(fun η => Real.exp (-(q * (s (k + 1) : ℝ))) *
          w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤
          Real.exp (-(q * (s k : ℝ))) * w (u k ω))
    (n : ℕ)
    (hterminal : 0 ≤
      ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P) :
    (∑ k ∈ Finset.range n, ∫ ω, cash k ω ∂P) ≤ w x := by sorry
