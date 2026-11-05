-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_immediate_ruin_strict_horizon_cash_le_candidate
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_immediate_ruin_strict_horizon_cash_le_candidate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:42:42.563292+00:00
-- url     : https://prove2.me/theorems/164cc5ff-1ded-4c4e-817a-01b3f0e91df0
-- title:
--   Original immediate-ruin true strict-horizon discounted Stieltjes Cash is bounded by the BV C1 candidate
-- statement:
--   At the exact initial ruin clock zero, the original left-continuous/right-payment controlled source has one permitted stopped payment time, time zero. For every strictly positive horizon T, the literal once-discounted Stieltjes integral over paymentTimes(ruinTime) intersect Iio T reduces to the original initial right dividend and is at most w(x) by source-verified h-jump and BV C1 gradient rules, with zero and cap boundary contact retained.
-- source:
--   Proved original paymentTimes zero 77cdd573, zero-horizon discounted cash 1fb597ac, initial HJB ledger 0315346e, BV C1 postpayment nonneg 28b04520.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_immediate_ruin_strict_horizon_cash_le_candidate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (ω : Ω) (q T : ℝ) (hT : 0 < T)
    (hruin : ruinTime X x D ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤ w x := by sorry
