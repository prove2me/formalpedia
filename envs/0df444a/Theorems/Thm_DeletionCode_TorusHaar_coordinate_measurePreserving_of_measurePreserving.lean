-- Prove2me | Theorems.Thm_DeletionCode_TorusHaar_coordinate_measurePreserving_of_measurePreserving
-- name    : DeletionCode.TorusHaar.coordinate_measurePreserving_of_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:33:45.154212+00:00
-- url     : https://prove2.me/theorems/376da211-cb4a-4372-9930-1c3377a765ed
-- title:
--   Torus Haar: coordinate measure Preserving of measure Preserving
-- statement:
--   Any random vector with the product Haar law has a uniform law in each coordinate.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L31-L35
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L31-L35

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

theorem DeletionCode.TorusHaar.coordinate_measurePreserving_of_measurePreserving
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume) (j : J) :
    MeasurePreserving (fun x => f x j) μ volume := by sorry
