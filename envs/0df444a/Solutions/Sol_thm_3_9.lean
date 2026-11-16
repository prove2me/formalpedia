-- Prove2me | solution 1 for thm_3_9
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:17.772137+00:00
-- url     : https://prove2.me/submissions/924f1b22-9f10-475b-a840-d60195d4bf0c

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Set


theorem solution (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  (h : ∀ x : ℝ, P (Iic x) = Q (Iic x)) :
  P = Q := by
  exact Measure.ext_of_Iic P Q h

