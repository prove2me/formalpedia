-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
-- name    : AvramDividend.Classical.avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:06:39.429194+00:00
-- url     : https://prove2.me/theorems/b09f3991-048d-483b-8cd4-5dfb82e41487
-- title:
--   Original perpetual dividend value bound from strict positive-horizon cash plus nonnegative terminal budgets
-- statement:
--   For one actual original IsAdmissible dividend strategy, suppose that at every strictly positive integer horizon n+1 there exists an ENNReal nonnegative terminal random variable such that the genuine original discounted dividendMeasure cash before ruin and strictly before n+1, plus that terminal, have total expected mass at most B. Then full dividendValue is bounded by B. The Proved closed-horizon iSup exhaustion, inclusion Iic(n) subset Iio(n+1), and monotonicity of inner and outer lintegrals justify the limit, preserving time-zero and every finite horizon atom. Terminal nonnegativity is built into ENNReal and terminal vanishing is never assumed. Handles q arbitrary and includes no circular stochastic assumptions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞)
    (hBudget : ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by sorry
