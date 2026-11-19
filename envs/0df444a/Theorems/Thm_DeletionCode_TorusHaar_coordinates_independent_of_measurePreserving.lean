-- Prove2me | Theorems.Thm_DeletionCode_TorusHaar_coordinates_independent_of_measurePreserving
-- name    : DeletionCode.TorusHaar.coordinates_independent_of_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:36:37.362196+00:00
-- url     : https://prove2.me/theorems/1345671e-d369-4d15-b049-b08e2ade99bf
-- title:
--   Torus Haar: coordinates independent of measure Preserving
-- statement:
--   A product Haar joint law implies joint independence, for any source measure.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L38-L51
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L38-L51

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

theorem DeletionCode.TorusHaar.coordinates_independent_of_measurePreserving
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume) :
    iIndepFun (fun j x => f x j) μ := by sorry
