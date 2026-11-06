-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_vanishing_closed_terminal_real_values
-- name    : AvramDividend.Classical.avram_limit2_strategywise_vanishing_closed_terminal_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:19:22.626203+00:00
-- url     : https://prove2.me/theorems/1f622a26-f3d5-4cb7-9db0-99a74208d36c
-- title:
--   Independent strategywise vanishing closed-window localisation errors to original cap/top real dividends
-- statement:
--   Each original capped-admissible strategy may have its own nonnegative localisation error sequence, eventually below every positive NNReal, and its own nonnegative terminal witnesses for closed Iic(n) stopped cash estimates with bound w x+error n. The same w bounds all original strategies because the per-strategy vanishing remainder passage removes each error independently before taking the strategy supremum. The result includes genuine real Stieltjes L1 and expected real payout bound plus capped and C=top unrestricted ENNReal value bounds.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_vanishing_remainder_closed_cash_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strategywise_vanishing_closed_terminal_real_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ error : ℕ → ℝ≥0∞,
          (∀ ε : ℝ≥0, 0 < ε →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n → error n ≤ (ε : ℝ≥0∞)) ∧
          (∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
            (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
              ENNReal.ofReal (w x) + error n)) :
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
