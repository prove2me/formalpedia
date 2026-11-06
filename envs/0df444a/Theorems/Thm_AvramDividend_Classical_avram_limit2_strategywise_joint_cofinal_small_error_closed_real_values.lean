-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_joint_cofinal_small_error_closed_real_values
-- name    : AvramDividend.Classical.avram_limit2_strategywise_joint_cofinal_small_error_closed_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:22:29.904614+00:00
-- url     : https://prove2.me/theorems/4ca4b569-698d-4e28-b5e5-28785b3fc467
-- title:
--   Strategywise joint cofinal closed original real perpetual dividends and capped/top bounds
-- statement:
--   For every actual original capped admissible strategy, arbitrarily remote closed deterministic cash horizons with arbitrarily small nonnegative errors and a nonnegative terminal budget control the true real perpetual Stieltjes dividend, integrability, capped value, and C=top unrestricted value. The error need only be small along cofinal horizons, not eventually at all horizons. Endpoint atoms follow the source closed convention.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_joint_cofinal_small_error_closed_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strategywise_joint_cofinal_small_error_closed_real_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ T : ℕ → ℝ,
          ∃ error : ℕ → ℝ≥0∞,
            (∀ ε : ℝ≥0, 0 < ε → ∀ a : ℝ,
              ∃ k : ℕ, a ≤ T k ∧ error k ≤ (ε : ℝ≥0∞)) ∧
            (∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
              (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                Iic (T k),
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
                ENNReal.ofReal (w x) + error k)) :
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
