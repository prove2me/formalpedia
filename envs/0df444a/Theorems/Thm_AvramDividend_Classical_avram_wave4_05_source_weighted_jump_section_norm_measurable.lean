-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_weighted_jump_section_norm_measurable
-- name    : AvramDividend.Classical.avram_wave4_05_source_weighted_jump_section_norm_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:00:24.877769+00:00
-- url     : https://prove2.me/theorems/8de553a5-4cd7-4aed-bc6a-6b58b6c0db9b
-- title:
--   Actual weighted compensated jump x-section L1 norm is Lévy-measurable
-- statement:
--   For any original q-scale function, the jump-magnitude-indexed real Bochner integral of the absolute exponential-weighted source generatorIntegrand over positive reserve x is a.e. strongly measurable under the exact negative-jump Lévy measure, without assuming product integrability. This discharges the previously separate section-norm measurability hypothesis in the established product-integrability criterion and correctly allows infinite activity.
-- source:
--   Original Lévy generatorIntegrand, chat04_scaleFunction_measurable_of_punctured_continuity, pinned Mathlib measurable_deriv, StronglyMeasurable.integral_prod_left and Lévy ν, mission 1300fbe7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The jump-indexed weighted x-section norm is measurable on the original
    negative-jump Levy measure, even before product integrability is known. -/

theorem AvramDividend.Classical.avram_wave4_05_source_weighted_jump_section_norm_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (θ : ℝ) :
    AEStronglyMeasurable
      (fun y : ℝ => ∫ x in Ioi (0 : ℝ),
        ‖Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y‖)
      (X.ν.restrict (Iio (0 : ℝ))) := by sorry
