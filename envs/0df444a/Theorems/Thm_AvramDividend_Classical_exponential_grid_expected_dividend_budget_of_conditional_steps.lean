-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_grid_expected_dividend_budget_of_conditional_steps
-- name    : AvramDividend.Classical.exponential_grid_expected_dividend_budget_of_conditional_steps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T17:06:00.483+00:00
-- url     : https://prove2.me/theorems/34502e3a-9e6c-4761-93e7-fa4b07575de4
-- title:
--   Exponential-discount finite-grid expected Stieltjes dividend precursor
-- statement:
--   For a sampled adapted dividend process and arbitrary real grid times s_k, suppose the one-step reserve value inequality has the discount factor exp(-q(s_(k+1)-s_k)), and the discounted cash and verification values are integrable. Then the expected sum of exp(-q s_k) times each dividend plus the final exp(-q s_n) verification value is bounded by the initial exp(-q s_0) verification value. Apply the already proved discounted finite-grid budget with alpha_k=exp(-q s_k) and beta_k=exp(-q(s_(k+1)-s_k)); the exponential addition law supplies alpha_(k+1)=alpha_k beta_k. This is a directly reusable bridge between the already proved Levy-adapted one-step stochastic bound and the BV/UV finite-horizon dividend-verification discretisation. The grid-to-Stieltjes approximation remains independent.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_dividend_budget_of_one_step_bounds

open MeasureTheory ProbabilityTheory

theorem AvramDividend.Classical.exponential_grid_expected_dividend_budget_of_conditional_steps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : Filtration ℕ mΩ)
    [SigmaFiniteFiltration P 𝓖]
    (u a : ℕ → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (s : ℕ → ℝ)
    (hCashI : ∀ k, Integrable (fun ω => Real.exp (-(q * s k)) * a k ω) P)
    (hVI : ∀ k, Integrable (fun ω => Real.exp (-(q * s k)) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      a k ω + Real.exp (-(q * (s (k + 1) - s k))) *
        (P[(fun η => w (u (k + 1) η)) | 𝓖 k]) ω ≤ w (u k ω))
    (n : ℕ) :
    (∑ k ∈ Finset.range n,
       ∫ ω, Real.exp (-(q * s k)) * a k ω ∂P) +
      (∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P) ≤
        (∫ ω, Real.exp (-(q * s 0)) * w (u 0 ω) ∂P) := by sorry
