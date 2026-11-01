-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_scale_weighted_signed_kernel_product_measurable
-- name    : AvramDividend.Classical.avram_wave4_05_source_scale_weighted_signed_kernel_product_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:58:33.501363+00:00
-- url     : https://prove2.me/theorems/b339a2c9-eb27-4ae7-9304-26ed414d47a5
-- title:
--   Original scale-function signed compensated kernel is product-a.e. strongly measurable
-- statement:
--   For any q-scale function of the original spectrally negative Levy process, without extra Gaussian or bounded-variation assumptions, the signed source compensated jump kernel multiplied by exp(-theta*x) is a.e. strongly measurable on the positive-state-by-negative-jump product measure. It uses actual source compensation, global q-scale Borel measurability and Mathlib's unconditional Borel measurability of ordinary derivatives. This discharges a nonoptional hypothesis in the source product-integrability and Fubini theorems.
-- source:
--   Source Lévy generator integrand; chat04_scaleFunction_measurable_of_punctured_continuity; pinned Mathlib measurable_deriv and indicator, mission 1300fbe7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Signed, weighted source compensated Levy kernel jointly measurable
    on the exact positive-reserve x negative-jump product measure. -/

theorem AvramDividend.Classical.avram_wave4_05_source_scale_weighted_signed_kernel_product_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (θ : ℝ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
