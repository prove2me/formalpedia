-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_strict_terminal_budgets_to_capped_and_top_values
-- name    : AvramDividend.Classical.avram_limit2_uniform_strict_terminal_budgets_to_capped_and_top_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:09:09.957191+00:00
-- url     : https://prove2.me/theorems/954faaf1-a00a-4e7e-b45d-d0ba7db9d055
-- title:
--   Uniform original strict cash plus nonnegative terminal budgets imply capped and unrestricted value bounds
-- statement:
--   For every actual nonnegative reserve within cap C and every original IsAdmissibleLe strategy, suppose the original discounted Stieltjes dividend cash before ruin and strictly before each positive integer horizon n+1, plus some ENNReal nonnegative terminal payoff, has expected mass at most ENNReal.ofReal(w x). The Proved source dividendValue_eq_iSup_truncated, genuine Iic(n) subset Iio(n+1), inner dividendMeasure and outer P lintegral monotonicity, and ENNReal nonnegative terminal yield a uniform per-strategy perpetual bound. The Proved local_verification_from_uniform_strategy_bound then gives both capped valueFunctionLe ≤ w and at C=top unrestricted valueFunction ≤ w, retaining actual strategy and original ruinTime. No terminal vanishing, sign restriction on q, stochastic martingale claim or equality in law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_uniform_strict_terminal_budgets_to_capped_and_top_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
          (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iio (((n + 1 : ℕ) : ℝ)),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
            ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
