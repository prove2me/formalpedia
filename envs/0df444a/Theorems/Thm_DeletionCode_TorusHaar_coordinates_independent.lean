-- Prove2me | Theorems.Thm_DeletionCode_TorusHaar_coordinates_independent
-- name    : DeletionCode.TorusHaar.coordinates_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:42:50.363622+00:00
-- url     : https://prove2.me/theorems/a89e2b7e-d03f-4ff2-b1c2-208ab1c993b3
-- title:
--   Torus Haar: coordinates independent
-- statement:
--   The output coordinates are jointly independent, including an empty output family.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L61-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L61-L65

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_DeletionCode_TorusHaar
set_option autoImplicit true
open DeletionCode DeletionCode.TorusHaar
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] DeletionCode.TorusHaar._p2m_local_instance_196a2ea6bd_18
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.TorusHaar.coordinates_independent
    (f : (I → UnitAddCircle) →+ (J → UnitAddCircle))
    (hcont : Continuous f) (hsurj : Function.Surjective f) :
    iIndepFun (fun j x => f x j) volume := by sorry
