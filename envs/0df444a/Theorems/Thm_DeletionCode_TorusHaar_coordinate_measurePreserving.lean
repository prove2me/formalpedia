-- Prove2me | Theorems.Thm_DeletionCode_TorusHaar_coordinate_measurePreserving
-- name    : DeletionCode.TorusHaar.coordinate_measurePreserving
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:42:46.442084+00:00
-- url     : https://prove2.me/theorems/9add7e90-1746-47aa-a387-b9fe0e6c07d9
-- title:
--   Torus Haar: coordinate measure Preserving
-- statement:
--   Every output coordinate has the uniform unit-circle law.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L54-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L54-L58

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

theorem DeletionCode.TorusHaar.coordinate_measurePreserving
    (f : (I → UnitAddCircle) →+ (J → UnitAddCircle))
    (hcont : Continuous f) (hsurj : Function.Surjective f) (j : J) :
    MeasurePreserving (fun x => f x j) volume volume := by sorry
