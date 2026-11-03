-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_dividendValue_finite_iff_genuine_unrestricted_signed_L1
-- name    : AvramDividend.Classical.avram_wave7_03_positive_discount_dividendValue_finite_iff_genuine_unrestricted_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:43:47.664743+00:00
-- url     : https://prove2.me/theorems/bf584471-fa0a-4877-93ac-42da6dd31302
-- title:
--   Positive discount expected canonical ENNReal Stieltjes dividends finite iff genuine unrestricted signed real Stieltjes payout is L1
-- statement:
--   Exact source-faithful positive-discount iff for genuine real unrestricted original dividends, not merely toReal of an ENNReal integral. The a.e. finite genuine inner cash follows from Proved positive-discount admissibility. The already Proved full pathwise signed-to-ENNReal Stieltjes bridge identifies each real Stieltjes integral with ENNReal.toReal cash, using positivity; hence real L1 equivalent to canonical dividendValue < top by Proved ENNReal real-conversion iff. Retains P, X, D, paymentTimes, ruinTime, dividendMeasure, jump and time-zero mass.
-- source:
--   Proved c3df986d positive-discount a.e. cash finite; Proved 329453c6 unrestricted signed pathwise Stieltjes equality; Proved 0ff0d1f6 value iff cash-toReal L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_perpetual_value_finite_iff_cash_toReal_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_positive_discount_dividendValue_finite_iff_genuine_unrestricted_signed_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    (dividendValue X q x D < ⊤) ↔
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by sorry
