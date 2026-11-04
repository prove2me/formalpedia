-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable
-- name    : AvramDividend.Classical.avram_p2_d_future_intrinsic_marked_rectangle_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:25:52.98914+00:00
-- url     : https://prove2.me/theorems/1f8f25b0-afb0-465f-8980-75f5ff35e3dc
-- title:
--   Original source intrinsic marked Borel rectangle count is measurable
-- statement:
--   For every original spectrally negative Lévy process and every Borel real-mark set B, the exact samplewise marked jump count N_X((s,t]×B), including infinite activity, is a measurable ENNReal-valued function of the original sample ω. This is the original-path measurable-functional interface for predictable marked-rate arguments.
-- source:
--   Apply the already Proved source s-finite kernel whose fibres are exactly the literal original jump measures, then compose Mathlib Measure.measurable_coe with Kernel.measurable at the Borel time–mark rectangle.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_intrinsic_marked_rectangle_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) := by sorry
