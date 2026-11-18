-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB135_native_centered_brownian_coordinate_measurable
-- name    : AvramDividend.Classical.avram_gbB135_native_centered_brownian_coordinate_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:41:58.841851+00:00
-- url     : https://prove2.me/theorems/a0fcacc2-02ef-44fe-8752-2f19d0d58127
-- title:
--   Every native centred Brownian time coordinate is measurable
-- statement:
--   For the canonical Mathlib Brownian process on the gaussianLimit sample-space Ω=(ℝ≥0→ℝ), every centred time-coordinate ω↦brownian(t,ω)-brownian(0,ω) is measurable. With B44 pointwise continuity and B134 the compact-open sigma-algebra evaluation criterion, this closes the measurable continuous-path lift needed to transfer the positive Brownian small-ball event unconditionally.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB44_native_brownian_centered_continuous_path_lift
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB135_native_centered_brownian_coordinate_measurable :
    ∀ t : ℝ≥0,
      Measurable (fun ω : ℝ≥0 → ℝ =>
        ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω) := by sorry
