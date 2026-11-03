-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_lower_discount_uniform_signed_budget_implies_higher_full_value
-- name    : AvramDividend.Classical.avram_wave7_03_original_lower_discount_uniform_signed_budget_implies_higher_full_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:36:49.965691+00:00
-- url     : https://prove2.me/theorems/cc012ec4-d4bc-4d09-8311-e88af79c5823
-- title:
--   Original signed finite-horizon uniform budget at lower discount transports to full higher-discount ENNReal dividendValue
-- statement:
--   On the identical original Levy path space and actual dividendMeasure, assume source Stieltjes finite mass almost surely at all natural positive horizons and genuine real L1(P) of both discounted finite-horizon signed payouts. A uniform real bound B on the expected signed Stieltjes cash at q₁≥0 therefore bounds every expected finite horizon at q₂≥q₁. The already verified full signed-to-ENNReal original source bridge upgrades this to dividendValue X q₂ x D ≤ ENNReal.ofReal B. Time-zero right-limit atom, all continuous/jump cash and strict pre-ruin stopping remain exactly in source definitions, without a substitute measure or stochastic HJB claim.
-- source:
--   Accepted genuine expected signed discount-order theorem e6cb3440, accepted canonical uniform signed horizon budget ⇒ full dividendValue theorem 96f0eeb7, source IsAdmissibleLe and nonnegative q₂.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_expected_signed_horizon_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_lower_discount_uniform_signed_budget_implies_higher_full_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (B : ℝ)
    (hfinite : ∀ n : ℕ, ∀ᵐ ω ∂P, (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ))) ≠ ⊤)
    (hInt₁ : ∀ n : ℕ, Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) P)
    (hInt₂ : ∀ n : ℕ, Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) P)
    (hBudget₁ : ∀ n : ℕ, (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((n + 1 : ℕ) : ℝ)),
      Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q₂ x D ≤ ENNReal.ofReal B := by sorry
