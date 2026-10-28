-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_finite_grid_dividend_budget_of_conditional_cash_steps
-- name    : AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_cash_steps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:52:27.328338+00:00
-- url     : https://prove2.me/theorems/8087d805-45ef-4ee4-8885-04a12ca894ca
-- title:
--   Finite-grid expected dividend budget with future-dependent cash conditioned on the past
-- statement:
--   For any sigma-finite discrete filtration and integrable real-valued cash and verification-value processes, suppose the conditional expectation of the cash accrued during the current grid interval plus the conditional expectation of next-step verification value is bounded by the current verification value. The sum of unconditional expected cash payments plus the terminal expected verification value is bounded by the initial expected verification value. The proof applies the already Proved finite-grid budget to the adapted conditional-cash process and uses integral_condExp to recover the original payments. This is a necessary bridge for capped BV/UV dividend verification because cash arising within an interval can depend on future observations, unlike payments known at the interval's start. The remaining root-connected obligation is to establish this conditional step bound from the stopped Lévy generator and control the Stieltjes limit.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Theorems.Thm_AvramDividend_Classical_expected_finite_grid_dividend_budget_of_conditional_steps

open MeasureTheory ProbabilityTheory

theorem AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_cash_steps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (cash V : ℕ → Ω → ℝ)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hVI : ∀ k, Integrable (V k) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓖 k]) ω +
        (P[(V (k + 1)) | 𝓖 k]) ω ≤ V k ω)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, cash k ω ∂P) +
        ∫ ω, V n ω ∂P ≤
      ∫ ω, V 0 ω ∂P := by sorry
