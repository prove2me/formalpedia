-- Prove2me | solution 1 for contourIntegrable_circleMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:07.818556+00:00
-- url     : https://prove2.me/submissions/76ff1ec0-bd3d-451b-a9e5-c287447a3603

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution {f : ℂ → F} {c : ℂ} (R : ℝ) :
    ContourIntegrable f (circleMap c R) ↔ CircleIntegrable f c R :=
  (circleIntegrable_iff R).symm
