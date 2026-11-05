-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_ruin_by_horizon_closed_cash_eq_strict_cash
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_ruin_by_horizon_closed_cash_eq_strict_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:33:29.234374+00:00
-- url     : https://prove2.me/theorems/837b141e-5a0d-431e-ad1b-f1a50a579929
-- title:
--   Original BV ruin-before-horizon complete real Stieltjes Cash equals strict horizon Cash
-- statement:
--   For the actual original X and D and a positive real T, whenever the true ruinTime is no later than T, the complete physical closed-horizon Stieltjes Cash is exactly the strict-horizon Cash; the original paymentTimes restriction already excludes the terminal right atom on that event. This treats the killed-terminal branch of the main P3 signed budget without discarding any cash.
-- source:
--   Proved 0e0c52cb source original paymentTimes terminal atom exclusion when actual ruin clock has ended.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_no_terminal_payment_if_clock_ended
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_ruin_by_horizon_closed_cash_eq_strict_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q T : ℝ)
    (hT : 0 < T)
    (hruin_le : ruinTime X x D ω ≤ ENNReal.ofReal T) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
