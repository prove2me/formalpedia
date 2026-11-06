-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_unrestricted_real_variational_sup
-- name    : AvramDividend.Classical.avram_limit2_ae_cofinal_unrestricted_real_variational_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:50:30.790792+00:00
-- url     : https://prove2.me/theorems/ef99c154-1e80-476f-afa6-69adb591038a
-- title:
--   Uniform original random-clock terminal budgets give unrestricted real dividend L1 variational equality
-- statement:
--   Assume every original unrestricted admissible strategy admits a measurable monotone random-clock localisation increasing to its true ruinTime almost surely, together with explicit nonnegative ENNReal terminal contributions so each closed integer-horizon stopped expected payout-plus-terminal is bounded by a finite ENNReal budget B. The Proved original LIMIT-1 a.e.-cofinal terminal budget theorem bounds the genuine unrestricted valueFunction by B. Consequently every admissible dividendValue is finite, and the Proved original full perpetual signed Stieltjes theorem gives real L1 integrability and exact expected payout identity for each original strategy. Rewriting the original double iSup yields an exact real variational representation of unrestricted valueFunction, retaining time-zero and right-closed cash atoms without equality-in-law or terminal vanishing.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ae_cofinal_terminal_budgets_to_unrestricted_value
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ae_cofinal_unrestricted_real_variational_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) (B : ℝ≥0∞)
    (hB : B < ⊤)
    (hBudget : ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissible X x D →
      ∃ σ : ℕ → Ω → ℝ≥0∞,
        (∀ k : ℕ, Measurable (σ k)) ∧
        (∀ ω : Ω, Monotone (fun k : ℕ => σ k ω)) ∧
        (∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω) ∧
        ∃ Terminal : ℕ → Ω → ℝ≥0∞,
          ∀ n k : ℕ,
            (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) +
              Terminal k ω) ∂P) ≤ B) :
    valueFunction X q x ≤ B ∧
    (∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D),
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) ∧
    valueFunction X q x =
      ⨆ (D : ℝ≥0 → Ω → ℝ), ⨆ (_ : IsAdmissible X x D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
