-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postzero_restart_nofuturejump_cash_le_drift
-- name    : AvramDividend.Classical.avram_bv_zero13_original_postzero_restart_nofuturejump_cash_le_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:27:22.45678+00:00
-- url     : https://prove2.me/theorems/86361ed9-dbaf-41df-9dbc-f4979ff68175
-- title:
--   Original finite-activity BV postpayment-zero restart dividend cash bounded by physical drift before next negative jump
-- statement:
--   For the original bounded-variation negative finite-jump-activity process and any admissible adapted dividend strategy, consider two ordered pathwise times with a source increment equal to physical drift times duration. If postpayment reserve is zero at the first time and nonnegative at the second, the actual half-open Stieltjes dividend cash is at most physical drift accrued. The second reserve may be positive and dividends may behave arbitrarily within the interval. This strengthens the existing both-end-zero equality to an excursion-start envelope, needed for arbitrary adapted departures from zero before the next original negative jump. It accounts for dividend right-payment chronology through rightLimit, excluding the first endpoint atom.
-- source:
--   Uses original riskProcess algebra and proved dividendMeasure_Ioc_rightLimit with IsAdmissibleLe; physical source no-negative-jump drift equality may be supplied by Proved 2a0cae7c. Consumer finite/top original BV stopped HJB budget.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_postzero_restart_nofuturejump_cash_le_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hzeroa : riskProcess X x D a ω -
      (rightLimit D a ω - D a ω) = 0)
    (hpositiveb : 0 ≤ riskProcess X x D b ω -
      (rightLimit D b ω - D b ω))
    (hline : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ))) := by sorry
