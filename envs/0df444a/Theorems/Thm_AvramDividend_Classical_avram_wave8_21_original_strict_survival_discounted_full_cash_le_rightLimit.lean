-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
-- name    : AvramDividend.Classical.avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:54:57.833931+00:00
-- url     : https://prove2.me/theorems/86168e67-e783-4efd-8a01-225fc7a4a993
-- title:
--   Exact original strict-survival complete discounted Stieltjes cash bounded by rightpayment cumulative mass
-- statement:
--   For each original dividend strategy, path and nonnegative horizon strictly before ruin, the full discounted ENNReal Stieltjes cash on paymentTimes intersect Iic T is bounded by ENNReal.ofReal (rightLimit D T ω), for q≥0. The integrator is exactly dividendMeasure D ω; time-zero and terminal rightpayment atoms and all atomless mass remain included.
-- source:
--   Original dividendMeasure and paymentTimes, the W8-21 proven strict-survival closed-horizon mass identity and Mathlib lintegral_indicator_one.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (rightLimit D T ω) := by sorry
