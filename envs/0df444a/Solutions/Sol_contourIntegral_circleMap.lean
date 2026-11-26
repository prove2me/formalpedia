-- Prove2me | solution 1 for contourIntegral_circleMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:03.811864+00:00
-- url     : https://prove2.me/submissions/22a36e70-f712-4988-a9cc-95d802595767

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution (f : ℂ → F) (c : ℂ) (R : ℝ) :
    contourIntegral f (circleMap c R) = circleIntegral f c R := rfl
