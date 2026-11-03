-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_signed_cash_le_rightLimit
-- name    : AvramDividend.Classical.avram_wave8_21_original_strict_survival_signed_cash_le_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:53:14.176172+00:00
-- url     : https://prove2.me/theorems/53d9521a-5ce6-49be-b347-4f076c1d85da
-- title:
--   Original signed strict-survival complete discounted Stieltjes cash bounded by cumulative rightpayment
-- statement:
--   For the original dividendMeasure D ω on paymentTimes before a strictly surviving horizon, the signed real-valued discounted Stieltjes cash is at most cumulative rightpayment when its real rightLimit is nonnegative. The proof combines the already Proved W7-03 identical-domain real-to-ENNReal conversion with the already Proved closed-horizon Stieltjes budget and the accepted original strict-survival payment set identity. There is no Open theorem import and no surrogate measure.
-- source:
--   Original dividendMeasure D ω; Proved W7-03 exact real/ENNReal bridge, Proved W3-03 full closed-horizon Stieltjes budget, accepted W8-21 paymentTimes identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_strict_survival_signed_cash_le_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω)
    (hRight : 0 ≤ rightLimit D T ω) :
    (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
        rightLimit D T ω := by sorry
