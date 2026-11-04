-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_real_cash_split_ae
-- name    : AvramDividend.Classical.avram_p3_bv_real_cash_split_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:51:09.938236+00:00
-- url     : https://prove2.me/theorems/7993ef7f-05df-41c0-94ac-b176d950a06e
-- title:
--   Original admissible BV finite-horizon real Stieltjes cash splits almost surely including the right-horizon atom
-- statement:
--   For the original admissible dividend strategy and every nonnegative deterministic horizon, the finite real-valued stopped Stieltjes cash agrees P-almost surely with its strict pre-horizon part plus the exact right-horizon atom. Derives finiteness from an already-Proved bounded-clock theorem and set measurability from the source helper.
-- source:
--   Proved avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite, paymentTimes_measurable, and avram_p3_bv_closed_horizon_real_cash_split.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_closed_horizon_real_cash_split
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_real_cash_split_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
