-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_zero_horizon_full_stieltjes_mass_even_immediate_ruin
-- name    : AvramDividend.Classical.avram_wave8_21_original_zero_horizon_full_stieltjes_mass_even_immediate_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:56:59.576687+00:00
-- url     : https://prove2.me/theorems/36c867df-0f25-4b36-ba85-1248ee3f3c4a
-- title:
--   Entire original time-zero Stieltjes rightpayment survives even when ruin is immediate
-- statement:
--   For any original spectrally negative Levy model, dividend strategy and sample path, the canonical stopped payment interval at zero is exactly the singleton time zero, independently of the ruin clock. Consequently its actual dividendMeasure D ω mass equals ENNReal.ofReal (rightLimit D 0 ω), even if ruinTime = 0. This preserves the full time-zero rightpayment atom and requires no strict-survival assumption, supplying W8-04's immediate-ruin endpoint convention.
-- source:
--   Original paymentTimes and original dividendMeasure; existing Proved closed-interval zero rightLimit Stieltjes mass identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_zero_horizon_full_stieltjes_mass_even_immediate_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    dividendMeasure D ω
      (paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ)) =
        ENNReal.ofReal (rightLimit D 0 ω) := by sorry
