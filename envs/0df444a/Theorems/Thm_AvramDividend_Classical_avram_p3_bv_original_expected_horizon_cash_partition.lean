-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_expected_horizon_cash_partition
-- name    : AvramDividend.Classical.avram_p3_bv_original_expected_horizon_cash_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:11:07.185873+00:00
-- url     : https://prove2.me/theorems/240c34cd-f5f5-44bf-a4ca-ac9837492bfb
-- title:
--   Original BV exact expected discounted Stieltjes cash partition at the right horizon atom
-- statement:
--   For the actual original spectrally negative Levy X and original admissible cap strategy D, the expected full discounted Stieltjes payout over paymentTimes(ruin) intersection (-infinity,T] equals the sum of the strict T payout and the single T right-payment atom, with no separate integrability hypothesis. This uses the true original dividendMeasure, includes the time-zero atom in the strict term whenever T is positive, and is valid at T=0. The result is independent of the generator and jump compensator, so may be imported by the final stopped Ito budget to restore the horizon atom exactly.
-- source:
--   Original almost-sure real-valued horizon cash decomposition 7993ef7f, original strict cash L1 67a9c5bf, original horizon atom L1 30776939, and Mathlib integral_congr_ae and integral_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_expected_horizon_cash_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) := by sorry
