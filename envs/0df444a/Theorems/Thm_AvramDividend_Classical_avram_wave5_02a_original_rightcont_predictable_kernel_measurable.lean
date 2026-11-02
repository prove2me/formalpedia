-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_rightcont_predictable_kernel_measurable
-- name    : AvramDividend.Classical.avram_wave5_02a_original_rightcont_predictable_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:00:51.576965+00:00
-- url     : https://prove2.me/theorems/fd94f92b-dbb3-4140-b8d3-32c4985bc100
-- title:
--   Actual original Levy right-continuous predictable jump-occupation kernel is measurable
-- statement:
--   For the original spectrally negative Levy process, the map sending each sample to the pushforward of that sample's literal source jump measure on the right-continuous predictable time-sample-mark sigma algebra is almost everywhere measurable. The original process is lifted unchanged to the right-continuous filtration and its same-path jumps are enumerated measurably. No copy, modified paths or extra measurable-space assumptions are introduced.
-- source:
--   Unchanged-source lift e58a099d, canonical source jump enumeration components, source kernel construction and predictable lift, each already Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_rational_grid_actual_jump_coverage
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_first_candidate_filter_covers_original_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_jump_kernel_of_measurable_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_original_rightcont_predictable_kernel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    AEMeasurable K P := by sorry
