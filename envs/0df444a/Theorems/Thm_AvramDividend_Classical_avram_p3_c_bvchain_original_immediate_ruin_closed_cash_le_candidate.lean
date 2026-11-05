-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_immediate_ruin_closed_cash_le_candidate
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_immediate_ruin_closed_cash_le_candidate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:29:20.818879+00:00
-- url     : https://prove2.me/theorems/a1cc2577-fb1d-45b0-848d-d2598e77e2b0
-- title:
--   Original BV immediate-ruin full closed-horizon rightpayment Cash is bounded by w(x)
-- statement:
--   For the actual original controlled source at immediate ruin and any positive horizon, the full literal closed Stieltjes dividend cash on paymentTimes(ruinTime) intersect Iic T is bounded by w(initial capital), retaining the complete initial right-payment even when the ruin clock equals zero. The strict survival terminal is zero on this event.
-- source:
--   Original immediate-ruin full paymentTimes={0} support and already Proved 164cc5ff strict-time-zero right cash budget.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_immediate_ruin_strict_horizon_cash_le_candidate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_immediate_ruin_closed_cash_le_candidate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q T : ℝ) (hT : 0 < T)
    (hruin : ruinTime X x D ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤ w x := by sorry
