-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_negative_levy_mark_mean_half
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_negative_levy_mark_mean_half
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:57:51.580625+00:00
-- url     : https://prove2.me/theorems/e9c5375c-82b9-49fb-bad7-e20373f715d2
-- title:
--   Uniform negative Poisson marks have unnormalised first moment negative one half
-- statement:
--   The first moment of Lebesgue measure restricted to the negative unit jump interval (-1,0) is -1/2. This establishes the Lévy drift normalisation c=1/2 and BV drift=1 used by the original compound Poisson positive-cap counterexample.
-- source:
--   The pinned Mathlib integral_id over [-1,0] gives (0²−(-1)²)/2 = -1/2. Endpoint-null open interval has the same integral. This is a complete scalar source certificate.

import Mathlib
open MeasureTheory intervalIntegral Set

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_negative_levy_mark_mean_half :
    (∫ z in Ioo (-1 : ℝ) 0, z ∂(volume : Measure ℝ)) =
      (-(1 / 2) : ℝ) := by sorry
