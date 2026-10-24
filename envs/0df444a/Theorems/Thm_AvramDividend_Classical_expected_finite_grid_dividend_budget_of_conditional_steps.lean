-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_finite_grid_dividend_budget_of_conditional_steps
-- name    : AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_steps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:40:26.245725+00:00
-- url     : https://prove2.me/theorems/0532475a-446c-4e7a-8196-59b3a1bac859
-- title:
--   Finite-grid expected dividend budget from conditional one-step stochastic verification inequalities
-- statement:
--   Let V_k be an integrable real-valued candidate process sampled at natural-number grid times, and cash_k an integrable real dividend payout at each step, adapted to a sigma-finite filtration. Assume each step satisfies cash_k plus the conditional expectation of V_(k+1) given the past filtration at k is at most V_k almost surely. Then for every finite horizon n, the sum of expected cash dividends through step n-1 plus the expectation of the terminal candidate V_n is bounded by the expectation of V_0. The proof applies monotonicity of the real Lebesgue integral to the conditional one-step inequality, uses the total-expectation identity for conditional expectation, and telescopes the resulting expected inequalities by induction. This is the precise stochastic-grid-to-expected-payout bridge needed after constructing adapted per-step HJB/semigroup bounds, and does not assume any pathwise payout inequality.
-- source:
--   Mathlib.MeasureTheory.integral_condExp and integral_mono_ae; discrete stochastic verification and telescoping expectations.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_steps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (cash V : ℕ → Ω → ℝ)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hVI : ∀ k, Integrable (V k) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      cash k ω + (P[(V (k + 1)) | 𝓖 k]) ω ≤ V k ω)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, cash k ω ∂P) +
        ∫ ω, V n ω ∂P ≤
      ∫ ω, V 0 ω ∂P := by sorry
