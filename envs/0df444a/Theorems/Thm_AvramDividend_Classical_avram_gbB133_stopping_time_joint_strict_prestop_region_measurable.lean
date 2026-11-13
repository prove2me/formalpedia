-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB133_stopping_time_joint_strict_prestop_region_measurable
-- name    : AvramDividend.Classical.avram_gbB133_stopping_time_joint_strict_prestop_region_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:09:57.512812+00:00
-- url     : https://prove2.me/theorems/0a814db7-dd24-41a8-925a-7c466d2e0130
-- title:
--   Joint measurability of a strict pre-stopping-time region
-- statement:
--   A stopping time with respect to the right-continuous filtration is a measurable WithTop-valued function. Compare it with the measurable embedded time coordinate in the product. The strict pre-stopping-time region is measurable, supplying the stopping indicator needed for B127.
-- source:
--   Mathlib IsStoppingTime.measurable and measurableSet_lt.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
open MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB133_stopping_time_joint_strict_prestop_region_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    MeasurableSet {z : ℝ≥0 × Ω | z.1 < ρ z.2} := by sorry
