-- Prove2me | Theorems.Thm_DeletionCode_TorusHaar_measurePreserving
-- name    : DeletionCode.TorusHaar.measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:33:37.291296+00:00
-- url     : https://prove2.me/theorems/cd8ca0d6-2489-4852-af0e-8a5294ad0b6a
-- title:
--   Torus Haar: measure Preserving
-- statement:
--   A continuous surjection of finite tori preserves their probability Haar laws.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L24-L28
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L24-L28

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

theorem DeletionCode.TorusHaar.measurePreserving
    (f : (I → UnitAddCircle) →+ (J → UnitAddCircle))
    (hcont : Continuous f) (hsurj : Function.Surjective f) :
    MeasurePreserving f volume volume := by sorry
