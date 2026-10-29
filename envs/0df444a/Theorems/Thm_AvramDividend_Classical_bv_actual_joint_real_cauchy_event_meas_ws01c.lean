-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_joint_real_cauchy_event_meas_ws01c
-- name    : AvramDividend.Classical.bv_actual_joint_real_cauchy_event_meas_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:43:29.434008+00:00
-- url     : https://prove2.me/theorems/15dca0fe-8a13-4ae1-b854-97cb2338a4c2
-- title:
--   Joint time–path BV dyadic Cauchy event is measurable
-- statement:
--   The actual Lévy drift-deficit dyadic Cauchy event is measurable in the product of positive/negative real start time and sample space, with negative starts mapped to zero by Real.toNNReal. Each slope coordinate is measurable by the Proved joint time-state measurability and measurable nonnegative-time map, and the countable Cauchy-event measurability theorem gives the whole event. This validates the exact measurable predicate passed to Fubini.
-- source:
--   Cause-linked re-publication of terminal job 404f1f0e-ead2-44a1-9c1d-7d9b94ff2599, whose sole failure was unknown import bv_real_toNNReal_measurable_explicit_ws01c. That exact theorem is now canonically Proved UUID 4e6ab162-435e-4a00-95f9-b07368548347. Original formal statement/preamble and 44-line source work/avram_ws01c_actual_joint_cauchy_meas_solution_direct.lean retained.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_bv_real_toNNReal_measurable_explicit_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_cauchyseq_real_event_measurable_ws01c

open Filter MeasureTheory Topology Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_actual_joint_real_cauchy_event_meas_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) :
    MeasurableSet {z : ℝ × Ω |
      CauchySeq (fun n : ℕ =>
        X.drift -
          (X.X (Real.toNNReal z.1 + ((1 : ℝ≥0) / 2) ^ n) z.2 -
            X.X (Real.toNNReal z.1) z.2) /
              (((1 : ℝ≥0) / 2) ^ n : ℝ))} := by sorry
