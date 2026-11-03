-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:24:51.80669+00:00
-- url     : https://prove2.me/theorems/3794152d-4a35-496d-b893-ed3868ea4ebb
-- title:
--   Original BV strict complement: actual negative-jump generator and discount cover the positive physical drift at every interior reserve
-- statement:
--   In the strict drift-envelope complement of the actual controlled BV spectrally negative Lévy dividend model, the Lévy physical drift is strictly positive. At every reserve strictly inside the positive cap, the genuine source negative-mark generator integral together with q times the C1 HJB candidate dominates that drift. This follows from the exact original BV generator representation, derivative lower bound and generator HJB inequality; it is a local source-jump envelope and does not assume or conclude the missing predictable stopped expected compensation.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 4(i) BV generator and jump integral. Uses Proved source c8ba98f0 and strict complement helper d6705e01; precursor to expected source compensated jump bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
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
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x))
    (y : ℝ) (hy0 : 0 < y) (hyC : ENNReal.ofReal y < C) :
    0 < X.drift ∧ X.GeneratorIntegrable w y ∧
    X.drift ≤ q * w y -
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) := by sorry
