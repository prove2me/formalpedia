-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_finite_real_measure_ext_of_positive_right_rays
-- name    : AvramDividend.Classical.avram_a06_finite_real_measure_ext_of_positive_right_rays
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:22:46.376849+00:00
-- url     : https://prove2.me/theorems/33019e0d-adc8-4cfc-a2be-8f2fd1d6b02c
-- title:
--   Finite real measures supported on positive values are determined by their nonnegative right-ray masses
-- statement:
--   Two finite measures on the real line with the same total mass, whose first measure is supported on strictly positive reals, are equal when their masses on all rays (t, infinity) agree for every nonnegative threshold t.
-- source:
--   At t=0 the ray and common mass determine support of the second measure too. For t<0 both rays have total mass. For all t, complement identities imply equality on Iic(t), so Measure.ext_of_Iic applies.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_finite_real_measure_ext_of_positive_right_rays
    (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (hMass : μ Set.univ = ν Set.univ)
    (hSupport : μ (Set.Ioi 0) = μ Set.univ)
    (hRay : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioi t) = ν (Set.Ioi t)) :
    μ = ν := by sorry
