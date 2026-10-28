-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_dividend_budget_of_one_step_bounds
-- name    : AvramDividend.Classical.discounted_finite_grid_dividend_budget_of_one_step_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:54:15.945104+00:00
-- url     : https://prove2.me/theorems/1dbbaa73-5962-485f-a009-1d2074d32727
-- title:
--   Discounted finite-grid expected dividend budget from adapted conditional one-step bounds
-- statement:
--   Let u_k be sampled reserve states, a_k the one-step dividend payouts, w a candidate value function, and alpha_k nonnegative discount factors satisfying alpha_(k+1)=alpha_k beta_k. Suppose the discounted dividends and terminal values are integrable, and the payout plus beta_k times the conditional expectation of w(u_(k+1)) is bounded above by w(u_k) almost surely. Then the expected sum of discounted payouts over any finite grid, plus its discounted terminal candidate value, is at most the initial candidate expectation. This theorem is a precise bridge from the already proved Levy-adapted reserve HJB one-step semigroup bound to the already proved finite-grid dividend budget and hence the finite-horizon capped BV and UV verification branches. No grid-to-Stieltjes limit or stochastic Ito assumption is imported by this statement.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_expected_finite_grid_dividend_budget_of_conditional_steps

open MeasureTheory ProbabilityTheory

theorem AvramDividend.Classical.discounted_finite_grid_dividend_budget_of_one_step_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (u a : ℕ → Ω → ℝ) (w : ℝ → ℝ)
    (α β : ℕ → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hfactor : ∀ k, α (k + 1) = α k * β k)
    (hCashI : ∀ k, Integrable (fun ω => α k * a k ω) P)
    (hVI : ∀ k, Integrable (fun ω => α k * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + β k * (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω
        ≤ w (u k ω))
    (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, α k * a k ω ∂P) +
        (∫ ω, α n * w (u n ω) ∂P) ≤
      (∫ ω, α 0 * w (u 0 ω) ∂P) := by sorry
