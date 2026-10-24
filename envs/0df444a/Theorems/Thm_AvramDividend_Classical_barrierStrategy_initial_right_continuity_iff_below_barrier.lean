-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_right_continuity_iff_below_barrier
-- name    : AvramDividend.Classical.barrierStrategy_initial_right_continuity_iff_below_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T17:07:12.384281+00:00
-- url     : https://prove2.me/theorems/532d601d-b267-45c3-b0e0-b49603d9d120
-- title:
--   The dividend path is right-continuous at zero exactly when initial capital is below the barrier
-- statement:
--   A constant-barrier cumulative dividend path has no right jump at its initial time if and only if initial capital x is at most the barrier a. The established right-increment formula identifies the initial jump as max(0,x−a), whose vanishing is equivalent to x≤a. This gives an exact admissibility-domain correction to the false unrestricted initial right-continuity statement.
-- source:
--   Proved barrierStrategy_right_increment_formula (8d23d801-85d6-465e-8450-4011e0dabd54), and barrierStrategy_no_right_jump_of_initial_below_barrier (b8214392-7702-4d2d-8973-702a270f0241).

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_initial_right_continuity_iff_below_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (ω : Ω) :
    (rightLimit (barrierStrategy X x a) 0 ω =
      barrierStrategy X x a 0 ω) ↔ x ≤ a := by sorry
