-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_ae_cofinal_vanishing_stop_real_values
-- name    : AvramDividend.Classical.avram_limit2_strategywise_ae_cofinal_vanishing_stop_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:20:46.645414+00:00
-- url     : https://prove2.me/theorems/539cd643-5ae1-4e7e-8bdc-d5d3fb4821d5
-- title:
--   Original source a.e.-cofinal stopped localisation errors per strategy imply full real cash and cap/top value bounds
-- statement:
--   For every genuine original capped admissible strategy, its own measurable monotone σ_k stopping clocks increase almost surely to actual ruinTime, with ENNReal nonnegative terminal witnesses and strategy-dependent errors eventually below each positive NNReal. The exact accepted source stopped-clock vanishing-error theorem yields full dividendValue upper bound, genuine real Stieltjes L1 cash and equality of its expected real mean. Nonnegative w converts this into a real mean bound. The accepted local verification bridge lifts the per-strategy inequalities to capped and at C=top unrestricted value functions without assuming a uniform stopping-clock rate.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_stopping_vanishing_errors_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strategywise_ae_cofinal_vanishing_stop_real_values
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
              (∀ n k : ℕ,
                (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
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
