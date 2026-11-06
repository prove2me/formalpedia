-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_vanishing_closed_terminal_budgets_real_values
-- name    : AvramDividend.Classical.avram_limit2_uniform_vanishing_closed_terminal_budgets_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:19:11.074188+00:00
-- url     : https://prove2.me/theorems/f37a5509-866a-4882-b309-4803264cfd79
-- title:
--   All original capped and top admissible strategies, real Stieltjes payout under vanishing stopped budget remainders
-- statement:
--   Uniform genuine closed Iic(n) original positive cash plus arbitrary nonnegative ENNReal terminal estimates may carry one common error sequence eventually smaller than every positive NNReal. The per-strategy original vanishing remainder theorem gives actual dividendValue bound, real Stieltjes L1 integrability and exact original real expected payout. With source nonnegative w this gives expected real cash ≤w. The proved local verification combinator yields capped and at C=top the unrestricted value bound. This is an exact adapter for stochastic localisation remainders; no terminal vanishing and no equality in law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_vanishing_remainder_closed_cash_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_uniform_vanishing_closed_terminal_budgets_real_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → error n ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
          (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
            ENNReal.ofReal (w x) + error n) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D =
          ENNReal.ofReal (∫ ω,
            (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
