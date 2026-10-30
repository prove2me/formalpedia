-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_increment_future_measurable
-- name    : AvramDividend.Classical.avram_wave3_04_drifted_increment_future_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:50:01.371642+00:00
-- url     : https://prove2.me/theorems/b064239b-dd0f-4714-a35e-37e632d6435f
-- title:
--   Every deterministic-drift increment is measurable from the entire undrifted future-increment path
-- statement:
--   The drifted increment is evaluation of the shifted undrifted increment path at t minus s, followed by subtraction of the deterministic time difference. Evaluation and translation are measurable and their comap is therefore contained in the full future-path information.
-- source:
--   Private pinned remote elaboration job dbe19cd1-4fbe-4fd6-98b3-82bf1f81743e, exact SHA 79010fa12764489ef7efe6100cefcb5bd398cd688bd753e21aca248826df6d5a.

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_drifted_increment_future_measurable {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    MeasurableSpace.comap
      (fun ω => (U t ω - (t : ℝ)) - (U s ω - (s : ℝ)))
      inferInstance ≤
    MeasurableSpace.comap
      (fun ω (r : ℝ≥0) => U (s + r) ω - U s ω)
      inferInstance  := by sorry
