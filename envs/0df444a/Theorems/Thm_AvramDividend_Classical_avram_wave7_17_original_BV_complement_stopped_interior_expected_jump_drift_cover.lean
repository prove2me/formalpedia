-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_stopped_interior_expected_jump_drift_cover
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_stopped_interior_expected_jump_drift_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:58:35.615433+00:00
-- url     : https://prove2.me/theorems/b4a4ea2a-7049-4321-8910-90e7a3971c07
-- title:
--   Original BV strict complement actual ruin-stopped interior expected physical drift is covered by discounted negative Lévy-source jump generator
-- statement:
--   On the actual probability P and physical Lebesgue-time clock, restricted to the genuinely ruin-stopped original controlled BV source interior, the expected discounted positive physical drift integral is no larger than the expected discounted q-killing candidate minus the actual negative-mark Lévy generator integral. This uses the Proved original strict-complement positive drift and Proved original W7-02 predictable HJB sign pointwise, with explicit measurability and integrability of the true localised region. It does not assert the missing Itô–Meyer source jump compensation, nor that the boundary reserve has negligible occupation.
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i), actual source Lévy generator and finite physical-time expectation under stopped interior localisation. Depends only on Proved original strict-complement sharp drift theorem d6705e01 and Proved original W7-02 predictable discounted HJB sign a0879a2f, plus standard restricted-measure integral monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_stopped_interior_expected_jump_drift_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0) :
    let μ : Measure (ℝ≥0 × Ω) :=
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set (ℝ≥0 × Ω) :=
      {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Y p ∧ ENNReal.ofReal (Y p) < C}
    MeasurableSet S →
    IntegrableOn
      (fun p => Real.exp (-(q * (p.1 : ℝ))) * X.drift) S μ →
    IntegrableOn
      (fun p => Real.exp (-(q * (p.1 : ℝ))) *
        (q * w (Y p) - (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν))) S μ →
    (∫ p in S, Real.exp (-(q * (p.1 : ℝ))) * X.drift ∂μ) ≤
    (∫ p in S, Real.exp (-(q * (p.1 : ℝ))) *
      (q * w (Y p) - (∫ z in Iio (0 : ℝ),
        w (Y p + z) - w (Y p) ∂X.ν)) ∂μ) := by sorry
