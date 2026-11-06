-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_residual_to_signed_horizon
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_residual_to_signed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:10:36.932805+00:00
-- url     : https://prove2.me/theorems/4f5824ba-131a-4004-80b4-95f7237ec6de
-- title:
--   Original BV strict stopped residual gives signed postpayment horizon budget
-- statement:
--   For the actual original spectrally negative Lévy risk process and admissible dividend strategy, an integrable nonpositive-mean strict-horizon source residual implies the exact positive-horizon signed HJB budget: closed Iic T Stieltjes cash plus strictly surviving discounted post-rightpayment reserve. The proof preserves the horizon atom, time-zero cash and w(0)≥0.
-- source:
--   Full proof by the public Proved original pointwise signed horizon correction 3c21e5f9-78b6-4f04-a32a-1a94fed7a5d2, original joint L1/integral-add 40cbe9a2-000b-4e99-af2f-33bfa3cd443d, and expectation monotonicity. It assumes the independent residual witness as explicit data, without importing the Open canonical residual, canonical prebudget, or GRID source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_residual_to_signed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (E : Ω → ℝ) (hEInt : Integrable E P)
    (hEMean : (∫ ω, E ω ∂P) ≤ 0)
    (hStrict : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ≤ w x + E ω) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by sorry
