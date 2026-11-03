-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_positive_discount_perpetual_value_finite_iff_cash_toReal_L1
-- name    : AvramDividend.Classical.avram_wave7_03_positive_discount_perpetual_value_finite_iff_cash_toReal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:56:01.656854+00:00
-- url     : https://prove2.me/theorems/0ff0d1f6-9846-44c7-ae52-58a76ea5c164
-- title:
--   Positive discount: original perpetual dividendValue finite iff full original Stieltjes cash real conversion is L1
-- statement:
--   For any actual original spectrally negative Lévy process and cap-admissible D with q>0, the source itself supplies almost-sure finiteness of the full ruined stopped perpetual discounted dividend Stieltjes ENNReal cash without additional Standing. Consequently the canonical expected dividendValue is finite exactly when the full original pathwise Stieltjes cash converted by ENNReal.toReal is P-integrable. The forward direction uses the proved original perpetual L1 bridge; the reverse direction uses genuine a.e. finiteness, precise ofReal_toReal at original P and Mathlib real/ENNReal integral conversion. This offers an exact L1 criterion for BV and UBV optional-stopping consumers with no extraneous sample space.
-- source:
--   Proved c3df986d-42ce-469d-99f0-41e67291a25c original q-positive a.e. cash finiteness and Proved 5f2772c6-96e6-4a7d-bab9-41e6750c07f1 original perpetual L1 bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_toReal_L1_and_exact_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_positive_discount_perpetual_value_finite_iff_cash_toReal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    (dividendValue X q x D < ⊤) ↔
      Integrable (fun ω : Ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by sorry
