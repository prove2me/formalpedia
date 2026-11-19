-- Prove2me | Theorems.Thm_DeletionCode_TorusHaar_preimage_rectangle
-- name    : DeletionCode.TorusHaar.preimage_rectangle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:42:49.82652+00:00
-- url     : https://prove2.me/theorems/7cf7c9af-7cbf-4820-8b6e-72f61dc70f07
-- title:
--   Torus Haar: preimage rectangle
-- statement:
--   Measurable coordinate tests have exactly the product of their uniform probabilities.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L73-L83
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L73-L83

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

theorem DeletionCode.TorusHaar.preimage_rectangle
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → (J → UnitAddCircle)} (hf : MeasurePreserving f μ volume)
    (A : J → Set UnitAddCircle) (hA : ∀ j, MeasurableSet (A j)) :
    μ (f ⁻¹' Set.univ.pi A) = ∏ j, volume (A j) := by sorry
