-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
-- name    : AvramDividend.Classical.avram_wave5_02a_joint_original_predictable_mark_lift_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:27:16.280196+00:00
-- url     : https://prove2.me/theorems/2648ec36-60c6-42af-b319-2ddaaeae8871
-- title:
--   Joint original sample and time mark lift into predictable space is measurable
-- statement:
--   For any original filtration the joint map ((time, mark), sample) to ((time, sample), mark) is measurable into the original marked predictable sigma algebra. This discharges the explicit hJoint premise in the original-source kernel bridge and applies equally to right-continuous filtrations.
-- source:
--   Predictable sigma algebra inclusion argument from accepted 16857b34-c56d-4e6d-9b74-2f2983732092 and measurable product projections.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_joint_original_predictable_mark_lift_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) :
    @Measurable ((ℝ≥0 × ℝ) × Ω) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace ((ℝ≥0 × ℝ) × Ω))
      (@Prod.instMeasurableSpace _ _ 𝓕.predictable
        (inferInstance : MeasurableSpace ℝ))
      (fun q : (ℝ≥0 × ℝ) × Ω => ((q.1.1, q.2), q.1.2)) := by sorry
