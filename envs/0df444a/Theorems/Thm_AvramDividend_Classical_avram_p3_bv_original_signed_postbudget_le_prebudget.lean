-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_postbudget_le_prebudget
-- name    : AvramDividend.Classical.avram_p3_bv_original_signed_postbudget_le_prebudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:56:04.709206+00:00
-- url     : https://prove2.me/theorems/05cd664e-092b-40b5-86ef-591b28cc5be4
-- title:
--   Original signed full-horizon expected payout is bounded by the strict prepayment budget
-- statement:
--   For the genuine original BV Levy source and cap-admissible strategy, with the exact horizon right dividend atom and signed strict-survival postpayment reserve, the expected full cash plus postpayment candidate is no greater than the expected strict-horizon cash plus prepayment candidate. The required integrability is discharged unconditionally by the already Proved original strict prebudget L1 and full cash/signed terminal L1 results. This result requires only the actual explicit right-jump secant and C1/gradient hypotheses, and assumes no compensation, generator drift inequality or additional integrability premise.
-- source:
--   Proved pathwise joint horizon accounting, original prebudget L1 78fa7075, full cash+signed postterminal L1 e53a9ae1 and a849869c, and Mathlib integral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_signed_postbudget_le_prebudget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (∫ ω, CashClosed ω + Post ω ∂P) ≤
      (∫ ω, CashOpen ω + Pre ω ∂P) := by sorry
