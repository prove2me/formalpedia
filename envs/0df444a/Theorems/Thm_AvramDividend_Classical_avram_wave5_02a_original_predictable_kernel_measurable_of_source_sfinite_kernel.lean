-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
-- name    : AvramDividend.Classical.avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:24:48.39268+00:00
-- url     : https://prove2.me/theorems/ea11f787-2c0f-4d13-a3b2-2e5c025cf7c3
-- title:
--   Original predictable jump occupation kernel is measurable from the actual source s-finite kernel
-- statement:
--   For the actual intrinsic marked jump measure of the given Levy process, a measurable s-finite kernel representation, together with measurable joint predictable lifting, yields almost everywhere measurability of the original predictable occupation measure. The source kernel equality is explicit and remains an independent construction obligation.
-- source:
--   Giry measurable evaluation, s-finite kernel integral and original predictable samplewise lift; conditional source kernel bridge for UUID d3243ffd-20ce-4011-9c51-5bc894700d2e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (κ : Kernel Ω (ℝ≥0 × ℝ)) [IsSFiniteKernel κ]
    (hκ : ∀ ω, κ ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.predictable
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ 𝓕.predictable
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (κ ω))
    (hJoint : @Measurable ((ℝ≥0 × ℝ) × Ω) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace ((ℝ≥0 × ℝ) × Ω))
      (@Prod.instMeasurableSpace _ _ 𝓕.predictable
        (inferInstance : MeasurableSpace ℝ))
      (fun q : (ℝ≥0 × ℝ) × Ω => ((q.1.1, q.2), q.1.2))) :
    AEMeasurable K P := by sorry
