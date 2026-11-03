-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_paid_measure_finite
-- name    : AvramDividend.Classical.avram_wave8_21_original_strict_survival_paid_measure_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:43:49.89427+00:00
-- url     : https://prove2.me/theorems/9e09b676-ed8b-416d-9a0c-74d2f97cbe73
-- title:
--   Original strictly stopped Stieltjes payout measure is finite on its full payment horizon
-- statement:
--   Under strict horizon survival, the total original dividendMeasure D ω on actual paymentTimes intersect Iic T is finite. The mass includes the time-zero atom, horizon rightpayment and all continuous or singular-continuous payout, and is derived from the accepted exact original mass equality.
-- source:
--   Source-specific finite mass from accepted exact original strictly stopped Stieltjes mass equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_strict_survival_paid_measure_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω) :
    dividendMeasure D ω
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) < ⊤ := by sorry
