-- Prove2me | Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
-- name    : DeletionCode.IntegerTorusMap.jointHash_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:27:27.56985+00:00
-- url     : https://prove2.me/theorems/8d0f4d67-d2f2-49d4-841d-cea0023e4b4a
-- title:
--   Integer Torus Map: joint Hash apply
-- statement:
--   The Integer Torus Map construction uses the joint Hash apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L32-L34
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L32-L34

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

theorem DeletionCode.IntegerTorusMap.jointHash_apply (w : J → I → ℤ)
    (weights : I → UnitAddCircle) (j : J) :
    jointHash w weights j = weightedHash weights (w j) := by sorry

attribute [defeq] DeletionCode.IntegerTorusMap.jointHash_apply
