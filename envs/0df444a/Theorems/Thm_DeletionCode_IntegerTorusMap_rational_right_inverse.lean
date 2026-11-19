-- Prove2me | Theorems.Thm_DeletionCode_IntegerTorusMap_rational_right_inverse
-- name    : DeletionCode.IntegerTorusMap.rational_right_inverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:42:23.359278+00:00
-- url     : https://prove2.me/theorems/432a2a4f-cc10-44eb-a311-e201ba5b650c
-- title:
--   Integer Torus Map: rational right inverse
-- statement:
--   Full rational row rank gives a rational right inverse.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L45-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L45-L56

import Definitions.Def_DeletionCode_CircleHash
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_DeletionCode_IntegerTorusMap
set_option autoImplicit true
open DeletionCode DeletionCode.IntegerTorusMap
open scoped BigOperators Matrix
open CircleHash
variable {I J : Type*} [Fintype I]
variable [Fintype J]

theorem DeletionCode.IntegerTorusMap.rational_right_inverse [DecidableEq J] (A : Matrix J I ℚ)
    (h : LinearIndependent ℚ A.row) :
    ∃ B : Matrix I J ℚ, A * B = 1 := by sorry
