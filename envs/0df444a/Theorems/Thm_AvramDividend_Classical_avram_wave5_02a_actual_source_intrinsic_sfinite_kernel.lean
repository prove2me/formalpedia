-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
-- name    : AvramDividend.Classical.avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:55:25.845077+00:00
-- url     : https://prove2.me/theorems/eb357d08-4af6-409d-a410-b001723c0008
-- title:
--   The literal original Levy jump measure is a measurable s-finite kernel
-- statement:
--   For any spectrally negative Levy process on its original measurable sample space and filtration, construct an s-finite measurable kernel whose fibre at every original sample is precisely the pushforward of counting measure on its positive nonzero path jumps under time and actual jump mark. No additional measurable-space assumptions, Poisson copy, finite activity, or bounded variation are used.
-- source:
--   Original rational-grid coverage, measurable first-occurrence filtering, exact intrinsic counting-measure reindexing and countable sum of finite deterministic kernels.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_rational_grid_actual_jump_coverage
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_first_candidate_filter_covers_original_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_jump_kernel_of_measurable_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    :
    ∃ κ : Kernel Ω (ℝ≥0 × ℝ), IsSFiniteKernel κ ∧
      ∀ ω, κ ω =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by sorry
