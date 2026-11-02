-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
-- name    : AvramDividend.Classical.avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:56:29.981459+00:00
-- url     : https://prove2.me/theorems/d3243ffd-20ce-4011-9c51-5bc894700d2e
-- title:
--   Actual original Lévy intrinsic jump occupation fibre-integral is a.e. measurable from its predictable occupation kernel
-- statement:
--   For the literal original Lévy intrinsic jump occupation NX, its predictable lift K is assumed to be a.e. measurable on the original probability space. Any nonnegative marked predictable integrand H then has an a.e.-measurable original-source fibre integral ω↦∫ H((t,ω),z) NXω(dt,dz). The source fibre equality is an explicit measure-map integral identity, not a fictitious independent Poisson copy. This discharges positive and negative fibre measurability assumptions in the Proved original intrinsic signed occupation Fubini theorem 53b748dd.
-- source:
--   Proved original predictable sample lift UUID 95f32973; Mathlib pinned Measure.measurable_lintegral and Measurable.comp_aemeasurable. Exact literal source NX of X; still assumes source-kernel AEMeasurable hKmeas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ≥0∞)
    (hHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H) :
    AEMeasurable (fun ω => ∫⁻ p, H ((p.1, ω), p.2) ∂(NX ω)) P := by sorry
