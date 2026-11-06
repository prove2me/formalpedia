-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_capped_and_unrestricted_real_variational_values
-- name    : AvramDividend.Classical.avram_limit2_ae_cofinal_capped_and_unrestricted_real_variational_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:40:47.963718+00:00
-- url     : https://prove2.me/theorems/9e78538a-16bf-4608-a392-714b8c3ff351
-- title:
--   Original cofinal-clock budgets imply exact real perpetual capped and unrestricted variational values
-- statement:
--   For the genuine spectrally negative Lévy dividend model, suppose every capped admissible strategy at every nonnegative in-cap reserve has measurable increasing original random stop clocks approaching its ruinTime almost surely and uniform closed-integer-horizon expected original discounted cash-plus-nonnegative-terminal budgets of ENNReal.ofReal(w x). Under explicit nonnegativity of w at those reserves, the already-Proved exact capped a.e.-cofinal cash-to-L1 bridge bounds all capped value functions by the finite ceiling. The already-Proved finite-value real Stieltjes variational representation then identifies the valueFunctionLe with the supremum over actual IsAdmissibleLe strategies of the ENNReal.ofReal real ruin-stopped payout expectation. At C=top, the Proved unrestricted value bound and variational representation yield the exact same formula over actual IsAdmissible strategies. The time-zero cash and original ruin clock remain intact; no terminal vanishing or equality-in-law is assumed.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_ae_cofinal_all_strategies_real_L1
import Theorems.Thm_AvramDividend_Classical_avram_limit2_finite_capped_value_exact_real_variational_sup
import Theorems.Thm_AvramDividend_Classical_avram_limit2_finite_unrestricted_value_exact_real_variational_sup

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ae_cofinal_capped_and_unrestricted_real_variational_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_nonneg : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ σ : ℕ → Ω → ℝ≥0∞,
          (∀ k : ℕ, Measurable (σ k)) ∧
          (∀ ω : Ω, Monotone (fun k : ℕ => σ k ω)) ∧
          (∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω) ∧
          ∃ Terminal : ℕ → Ω → ℝ≥0∞,
            ∀ n k : ℕ,
              (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω)) +
                Terminal k ω) ∂P) ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x =
        ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissibleLe X x C D),
          ENNReal.ofReal
            (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x =
        ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissible X x D),
          ENNReal.ofReal
            (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) := by sorry
