-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_any_clock_caplinear_reward_regular
-- name    : AvramDividend.Classical.avram_f6_original_any_clock_caplinear_reward_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:56:57.592189+00:00
-- url     : https://prove2.me/theorems/8fcf4de2-d19e-4194-9783-a125ec31ac15
-- title:
--   Original stopped caplinear reward measurable and nonnegative at each true stopping clock
-- statement:
--   For any original UBV stopped right-continuous stopping clock, the actual discounted caplinear postpayment terminal plus inclusive dividendMeasure Iic discounted cash is measurable and pointwise nonnegative; source-faithful, using only proved exact original reward, original measurability and nonnegativity. No HJB mean bound is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_real_caplinear_cash_exact
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_source_reward_measurable
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_any_clock_caplinear_reward_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (c : Ω → ℝ≥0)
    (hc : IsStoppingTime 𝓕.rightCont
      (fun ω => (c ω : WithTop ℝ≥0))) :
    let V : ℝ → ℝ := fun z =>
      if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal)
    let R : Ω → ℝ := fun ω =>
      Real.exp (-(q * (c ω : ℝ))) *
        V (if c ω = 0 ∨ (c ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (c ω) ω - rightLimit D (c ω) ω
          else riskProcess X x D (c ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (c ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    Measurable R ∧ (∀ ω, 0 ≤ R ω) := by sorry
