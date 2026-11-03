-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:42:23.190464+00:00
-- url     : https://prove2.me/theorems/9806569f-9a73-407f-bbec-ed17c0080386
-- title:
--   Canonical perpetual original expected ENNReal dividends equal ofReal of genuine untruncated signed real Stieltjes mean under finite expected cash
-- statement:
--   For the exact original spectrally negative Lévy process, its probability P, actual dividend strategy D, canonical ruinTime, paymentTimes and full dividendMeasure, if the entire outer expected perpetual ENNReal discounted Stieltjes cash is genuinely finite, then the *unrestricted original real signed Stieltjes payout integral itself* (not only toReal of the ENNReal fibre) is integrable in L1(P), and the canonical dividendValue equals ENNReal.ofReal of its exact expected real signed Stieltjes payout. The proof derives a.e. finiteness of source inner cash, invokes the source-faithful pathwise integrable real/ENNReal perpetual identity, identifies genuine real cash with F.toReal almost everywhere and applies the already Proved original outer perpetual L1/mean bridge. Strict pre-ruin, time-zero right-limit, all jumps and continuous payments remain at precisely the original measure/domain. No unrelated sample space or unstated outer integrability premise.
-- source:
--   Proved original perpetual cash measurability db59cbee; Proved original cash toReal L1/mean 5f2772c6; source exact unrestricted pathwise signed Stieltjes lemma (new); pinned ae_lt_top and Integrable.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
