-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux6_bv_single_clock_finite_cap_expected_budget
-- name    : AvramDividend.Classical.avram_redux6_bv_single_clock_finite_cap_expected_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T06:23:38.563462+00:00
-- url     : https://prove2.me/theorems/73419313-f2bf-4800-8f49-ddebb60eb188
-- title:
--   Original BV finite-cap single strict-clock stopped HJB expected budget
-- statement:
--   The genuine stopped BV source estimate at a fixed strict observation time and finite reserve cap. The finite range permits bounded-domain localisation, while time-zero right atoms, strict pre-ruin cash and the surviving terminal at T remain unchanged.
-- source:
--   Cap dichotomy of the exact original BV source theorem 51b72610. The parent will be formally reduced by C=top or C≠top, with no source modifications or stochastic result presumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux6_bv_single_clock_finite_cap_expected_budget
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
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ s : ℝ, 0 ≤ s → s < T →
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio s,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by sorry
