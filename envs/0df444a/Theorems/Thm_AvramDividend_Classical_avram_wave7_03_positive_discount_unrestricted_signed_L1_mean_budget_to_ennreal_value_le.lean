-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_unrestricted_signed_L1_mean_budget_to_ennreal_value_le
-- name    : AvramDividend.Classical.avram_wave7_03_positive_discount_unrestricted_signed_L1_mean_budget_to_ennreal_value_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:55:40.437287+00:00
-- url     : https://prove2.me/theorems/9486c502-bd76-4abb-ad23-ae7176b14979
-- title:
--   Positive-discount genuine unrestricted original signed real Stieltjes L1 expected budget directly bounds canonical ENNReal dividendValue
-- statement:
--   At q>0 for the exact original admissible dividend strategy, if the genuine unrestricted signed real discounted Stieltjes payout on original paymentTimes(ruinTime) and original dividendMeasure is integrable in L1(P) and its expected real payout ≤ B, the canonical double ENNReal dividendValue ≤ ENNReal.ofReal B. Positive discount admissibility ensures almost-sure finite paths automatically. This is a direct three-line consumer for the HJB signed budget branch, retaining time-zero right-limit atom, continuous and jump payments and strict pre-ruin stopping.
-- source:
--   Proved positive discount original genuine signed L1 iff bf584471; Proved original outer exact signed Stieltjes mean 9806569f; ENNReal.ofReal_le_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_dividendValue_finite_iff_genuine_unrestricted_signed_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_positive_discount_unrestricted_signed_L1_mean_budget_to_ennreal_value_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (hRealIntegrable : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P)
    (B : ℝ)
    (hRealBudget : (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q x D ≤ ENNReal.ofReal B := by sorry
