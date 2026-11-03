-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
-- name    : AvramDividend.Classical.avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:44:24.768948+00:00
-- url     : https://prove2.me/theorems/ea93e549-64e0-43bb-b06f-c2a2b7640f27
-- title:
--   Original strictly surviving closed-horizon Stieltjes payout mass equals the complete dividend right limit
-- statement:
--   On any sample path whose ruin time is strictly after the deterministic nonnegative horizon T, the canonical original dividendMeasure restricted to actual paymentTimes and the closed horizon has total ENNReal mass precisely equal to rightLimit D T ω. Both the time-zero rightpayment and the horizon's own rightpayment atom are included, alongside all continuous Stieltjes dividends; no surrogate measure or exclusion of boundary mass is introduced.
-- source:
--   Avram original Stieltjes dividendMeasure, paymentTimes strict stopping convention and proved closed-horizon right-limit identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω) :
    dividendMeasure D ω
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) =
        ENNReal.ofReal (rightLimit D T ω) := by sorry
