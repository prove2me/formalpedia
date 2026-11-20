-- Prove2me | Theorems.Thm_DeletionCode_TorusHaar_evaluations_independent
-- name    : DeletionCode.TorusHaar.evaluations_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:02.903877+00:00
-- url     : https://prove2.me/theorems/357042a8-8452-4f66-86d2-ea8ee8ec64e6
-- title:
--   Torus Haar: evaluations independent
-- statement:
--   The original product-coordinate variables are themselves independent.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L68-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean#L68-L70

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

theorem DeletionCode.TorusHaar.evaluations_independent :
    iIndepFun (fun i (x : I → UnitAddCircle) => x i) volume := by sorry
