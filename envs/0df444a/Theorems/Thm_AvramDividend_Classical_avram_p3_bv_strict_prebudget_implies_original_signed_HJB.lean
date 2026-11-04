-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_strict_prebudget_implies_original_signed_HJB
-- name    : AvramDividend.Classical.avram_p3_bv_strict_prebudget_implies_original_signed_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:38:37.847796+00:00
-- url     : https://prove2.me/theorems/6f9a6057-bba1-40e9-8688-16aa43a3faa3
-- title:
--   Original BV canonical signed HJB budget follows from genuine strict pre-horizon stochastic core
-- statement:
--   The original-source BV positive-horizon signed stopped dividend budget follows from exactly the genuine strict prepayment expected upper bound, together with already Proved original signed horizon payment accounting and exact full cash/terminal expectation additivity. The strict stochastic budget is explicit and unproved: this is solely a checked conditional assembly bridge; it does not close the canonical theorem or assert the jump compensator.
-- source:
--   Proved original signed postbudget comparison 05cd664e; Proved original cash plus signed terminal integral additivity 40cbe9a2; hypothesis is precisely the remaining actual-original-process stochastic HJB budget, not a P2 surrogate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_postbudget_le_prebudget
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_strict_prebudget_implies_original_signed_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hStrict :
      let S : ℝ≥0 := ⟨T, hT⟩
      let CashOpen : Ω → ℝ := fun ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
      let Pre : Ω → ℝ := fun ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
      (∫ ω, CashOpen ω + Pre ω ∂P) ≤ w x) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else 0
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by sorry
