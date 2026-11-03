-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_ae_all_horizons_ENNReal_toReal_eq_signed
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_ae_all_horizons_ENNReal_toReal_eq_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:54:24.157014+00:00
-- url     : https://prove2.me/theorems/5f04375d-f87d-44d2-8eb3-83a559e675bd
-- title:
--   Original finite dividendValue gives a.e exact real and ENNReal Stieltjes payout identity at every horizon
-- statement:
--   For an original spectrally negative Levy dividend strategy, finite actual dividendValue ensures that for P-almost every sample and every real horizon T, exact original pre-ruin discounted Stieltjes ENNReal payout toReal equals the signed real Stieltjes integral on paymentTimes ruin ∩ Iic T. Full original time-zero right-limit atom and continuous dividend mass retained.
-- source:
--   Proved original full-value finiteness theorem fd64314b, pathwise finite iff signed integrable a6d24d2f; pinned Mathlib exact ofReal integral equality.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_ae_all_horizons_ENNReal_toReal_eq_signed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal =
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
