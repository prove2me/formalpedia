-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_vanishing_strict_terminal_budgets_real_values
-- name    : AvramDividend.Classical.avram_limit2_uniform_vanishing_strict_terminal_budgets_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:19:49.156187+00:00
-- url     : https://prove2.me/theorems/d4a0ecf2-6801-4884-b63d-3b9f601c0c1b
-- title:
--   Uniform vanishing strict horizon source budget to original capped/top value and real Stieltjes mean
-- statement:
--   Uniform original Stieltjes cash on strict positive Iio(n+1) horizons plus arbitrary nonnegative terminal remainder, bounded by w x and a common nonnegative error sequence eventually smaller than every positive NNReal, yields real signed original payout integrability and bound for all original capped strategies. The previously Proved strict horizon exhaustion and vanishing remainder theorem yield per-strategy dividendValue; pinned local_verification_from_uniform_strategy_bound yields capped and C=top unrestricted value estimates. Time-zero and finite endpoint atoms are retained; no terminal vanishing or equality in law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_vanishing_remainder_strict_cash_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_uniform_vanishing_strict_terminal_budgets_real_values
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
          (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iio (((n + 1 : ℕ) : ℝ)),
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
