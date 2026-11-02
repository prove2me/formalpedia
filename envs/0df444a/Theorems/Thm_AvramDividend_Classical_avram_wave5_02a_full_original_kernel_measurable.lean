-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_full_original_kernel_measurable
-- name    : AvramDividend.Classical.avram_wave5_02a_full_original_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:58:28.581028+00:00
-- url     : https://prove2.me/theorems/4443ac3e-93d8-4f0a-9265-1cf193bc3331
-- title:
--   Actual original Levy predictable jump-occupation kernel is measurable
-- statement:
--   For every original spectrally negative Levy process on an arbitrary original measurable probability space, the measure-valued map obtained by pushing its literal intrinsic time-mark jump measure into original predictable time-sample-mark space is almost everywhere measurable. The proof constructs and enumerates the actual source jumps; it does not replace the process by an independent Poisson copy or assume kernel measurability.
-- source:
--   Actual rational-grid jump coverage, first-occurrence filtering, source counting-measure identity, source s-finite kernel construction and original predictable kernel lift. The coverage and counting identity must be canonically Proved before relying on this theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_rational_grid_actual_jump_coverage
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_first_candidate_filter_covers_original_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_jump_kernel_of_measurable_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_full_original_kernel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.predictable
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ 𝓕.predictable
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    AEMeasurable K P := by sorry
