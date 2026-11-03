-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_predictable_negative_kernel_L1_from_min_mark_weight
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_predictable_negative_kernel_L1_from_min_mark_weight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:34:00.743854+00:00
-- url     : https://prove2.me/theorems/27f8d32c-f566-4c1e-b24d-7f5dc34291b1
-- title:
--   Original BV predictable signed negative jump kernel is L1 under uniform min-one-absolute-mark envelope and finite physical clock
-- statement:
--   On the unchanged original spectrally negative Levy source, the genuine bounded-variation condition makes min(1,|z|) integrable with respect to the full original negative Levy measure. Hence any original right-continuous predictable measurable C1 negative-jump kernel dominated almost everywhere by the weight L*min(1,|z|) has finite product L1 against any finite actual physical predictable clock. This directly supplies the intensity-side integrability for exact stopped signed source compensation without an assumed integrable mark envelope or finite total jump activity. The envelope inequality remains an explicit measurable source-specific condition.
-- source:
--   Proved actual BV negative min-one moment 1f8249f1-4c55-4a8c-91df-cd677dacd4d9; Proved original physical predictable marked-envelope product L1 0fd3279a-04e0-4d8d-952f-7a555574df54.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_predictable_negative_kernel_L1_from_min_mark_weight
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
  (hμ : μ Set.univ < ⊤)
  (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hGm : Measurable[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
  (L : ℝ)
  (hBound : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable;
    ∀ᵐ p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))),
      ‖G p‖ ≤ ‖L * min 1 |p.2|‖)) :
  (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable;
    Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
