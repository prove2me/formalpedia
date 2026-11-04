-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_prebudget_to_full_signed_expectation
-- name    : AvramDividend.Classical.avram_p3_bv_prebudget_to_full_signed_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:26:57.138182+00:00
-- url     : https://prove2.me/theorems/df0f6a71-c23c-4a99-9d9c-ea0556797783
-- title:
--   Original BV pre-horizon expected verification implies exact full-horizon signed budget
-- statement:
--   Original-process conditional assembly bridge: if the strictly pre-horizon cash plus strictly surviving pre-rightpayment candidate value is integrable and has expected budget at most w(x), then the exact closed-horizon cash including the T atom and post-rightpayment signed terminal has the same budget. Postpayment L1 is discharged from already Proved source theorems, while the sole explicit remaining stochastic obligation is the pre-horizon HJB budget.
-- source:
--   Proved joint exact horizon accounting, original full cash L1 and signed surviving terminal L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_joint_horizon_terminal_accounting
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_prebudget_to_full_signed_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let CashOpen : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let CashClosed : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0
    let Post : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
      else 0
    Integrable (fun ω => CashOpen ω + Pre ω) P →
    (∫ ω, CashOpen ω + Pre ω ∂P) ≤ w x →
    (∫ ω, CashClosed ω + Post ω ∂P) ≤ w x := by sorry
