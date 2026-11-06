-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_strict_diagonal_stops_real_values
-- name    : AvramDividend.Classical.avram_limit2_strategywise_strict_diagonal_stops_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:31:27.909205+00:00
-- url     : https://prove2.me/theorems/346a1a86-f631-4c35-9445-ada06f44467e
-- title:
--   Strategywise original strict diagonal stopped cash and vanishing errors bound perpetual real capped and top dividends
-- statement:
--   For every original capped-admissible D, choose its own measurable increasing almost-everywhere cofinal ruin-stop clocks σ_k, nonnegative Terminal_k and asymptotically vanishing ENNReal errors. Only a single strict positive horizon Iio(k+1) stopped cash-plus-terminal budget at each clock k is assumed. The source-exact diagonal stopped-cash lemma gives each strategy genuine full dividendValue≤w(x), integrable real original Stieltjes payout and exact expected cash. The already Proved local verification combinator lifts to capped value and C=top unrestricted value bounds, with time-zero/right-horizon atoms preserved; no stochastic budget is falsely inferred.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_strict_diagonal_stopped_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strategywise_strict_diagonal_stops_real_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ σ : ℕ → Ω → ℝ≥0∞,
          (∀ k : ℕ, Measurable (σ k)) ∧
          (∀ ω : Ω, Monotone (fun k : ℕ => σ k ω)) ∧
          (∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω) ∧
          ∃ Terminal : ℕ → Ω → ℝ≥0∞,
            ∃ error : ℕ → ℝ≥0∞,
              (∀ ε : ℝ≥0, 0 < ε →
                ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞)) ∧
              (∀ k : ℕ,
                (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩
                  Iio (((k + 1 : ℕ) : ℝ)),
                  ENNReal.ofReal (Real.exp (-(q * t)))
                    ∂(dividendMeasure D ω)) + Terminal k ω) ∂P)
                ≤ ENNReal.ofReal (w x) + error k)) :
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
