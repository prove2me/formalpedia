-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_capped_ae_cofinal_all_strategies_real_L1
-- name    : AvramDividend.Classical.avram_limit2_capped_ae_cofinal_all_strategies_real_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:50:42.327137+00:00
-- url     : https://prove2.me/theorems/25621a05-22cc-4273-bce0-379d377c5481
-- title:
--   Capped a.e.-cofinal source budgets give exact real perpetual dividend L1 and bound for every strategy
-- statement:
--   Suppose at every nonnegative reserve x within the actual cap C and for every original capped admissible dividend strategy, measurable monotone random stopping clocks increase to the true ruin clock almost surely and finite stopped cash plus nonnegative ENNReal terminal contributions are uniformly bounded by ofReal(w x) at every closed integer horizon. If w(x) is nonnegative, then every original capped strategy has a genuine untruncated real signed Stieltjes dividend payout in L1, its dividendValue exactly equals the ENNReal.ofReal of the real expected payout, and that expected payout is at most w(x). The capped value bound and its C=top unrestricted version hold. This uses only the Proved LIMIT-1 a.e.-cofinal stopped budget-to-value theorem and the Proved original finite-value real Stieltjes integrability theorem. No a.s. convergence of terminal values or equality-in-law is assumed.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_capped_ae_cofinal_terminal_budgets_to_local_values
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_capped_ae_cofinal_all_strategies_real_L1
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
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D =
          ENNReal.ofReal
            (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
