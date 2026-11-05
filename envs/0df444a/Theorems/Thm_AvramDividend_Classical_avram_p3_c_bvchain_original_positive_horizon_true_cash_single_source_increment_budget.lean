-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_positive_horizon_true_cash_single_source_increment_budget
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_positive_horizon_true_cash_single_source_increment_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:02:52.265061+00:00
-- url     : https://prove2.me/theorems/a5ed17a4-e3ed-4861-931a-65189c351ea4
-- title:
--   Original BV C1 positive-horizon initial atom plus open cash single source increment budget
-- statement:
--   For any original admissible left-continuous/right-payment control and positive finite pre-ruin stopping horizon, full continuous and atomic discounted dividend cash including the time-zero atom and excluding the horizon atom, together with the discounted pre-rightpayment terminal, is bounded by w(initial reserve) plus the single frozen original source increment.
-- source:
--   Coarsest mesh n=0 specialization of Proved genuine original source frozen true cash bound dc8290b6-58e9-4df0-9dc2-4a280df547c4.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_true_cash_frozen_source_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_positive_horizon_true_cash_single_source_increment_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0) (hb : 0 < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (V (x + X.X b ω - rightLimit D 0 ω) -
        V (x + X.X 0 ω - rightLimit D 0 ω)) := by sorry
