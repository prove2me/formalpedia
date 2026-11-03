-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:24:04.957078+00:00
-- url     : https://prove2.me/theorems/c3df986d-42ce-469d-99f0-41e67291a25c
-- title:
--   Original discounted perpetual full-Stieltjes cash is finite almost surely for every positive discount
-- statement:
--   For arbitrary admissible original source reserve and dividends, with no standing or variation assumption, every positive discount rate ensures that the full untruncated Stieltjes cash flow stopped at ruin is finite for P-almost every original sample path. This concerns the ENNReal integral itself, not its toReal image, which would conceal infinite values.
-- source:
--   From source positive-small-tilt theorem 6b7f5580, original perpetual theta budget 2abbc6bc, original kernel measurability db59cbee, and Mathlib MeasureTheory.ae_lt_top. Directly needed for honest localised terminal cash conversion in corrected UBV stochastic inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ := by sorry
