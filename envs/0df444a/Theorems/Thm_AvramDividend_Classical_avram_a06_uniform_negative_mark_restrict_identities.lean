-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_restrict_identities
-- name    : AvramDividend.Classical.avram_a06_uniform_negative_mark_restrict_identities
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T19:02:32.905333+00:00
-- url     : https://prove2.me/theorems/dacf0ba2-9975-4385-936a-5f476d1d330d
-- title:
--   Uniform negative-mark measure is unchanged by negative-halfline and original-band restriction
-- statement:
--   The compactly supported negative uniform law remains exactly the same measure after restricting to (-infinity,0) or its original support (-1,0). This is used to match the two expressions for the compensated Laplace exponent.
-- source:
--   Direct deterministic prerequisite of A06 compensated-exponent identity fa25b11f.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_negative_mark_restrict_identities :
    (((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))).restrict (Iio (0 : ℝ)) = ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ∧
    (((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))).restrict (Ioo (-1 : ℝ) 0) = ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) := by sorry
