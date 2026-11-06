-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_closed_diagonal_stops_real_values
-- name    : AvramDividend.Classical.avram_limit2_strategywise_closed_diagonal_stops_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:15:43.745871+00:00
-- url     : https://prove2.me/theorems/10151ee4-6c12-448a-9958-2c835e903cf0
-- title:
--   Original strategy-dependent closed diagonal stopped cash and vanishing errors give real perpetual capped and top values
-- statement:
--   At each original positive reserve, each capped admissible strategy may choose its own measured monotone a.e.-cofinal ruin stopping clocks, nonnegative terminal rewards, and vanishing errors. Only the one diagonal expected cash bound at σ_k and closed Iic(k) is assumed. Once the genuine original closed diagonal stopped-cash theorem is proved, it supplies real L1 perpetual Stieltjes payouts and exact expected cash value, and local_verification_from_uniform_strategy_bound lifts per-strategy finite value bounds to capped and C=top unrestricted value. No stochastic budget inferred and no equality-in-law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_diagonal_stopped_vanishing_errors_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strategywise_closed_diagonal_stops_real_values
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
                (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (k : ℝ),
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
