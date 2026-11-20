-- Prove2me | Theorems.Thm_DeletionCode_IntegerTorusMap_real_right_inverse
-- name    : DeletionCode.IntegerTorusMap.real_right_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:42:29.465218+00:00
-- url     : https://prove2.me/theorems/7d971b61-2c4b-4084-812e-ee677d27f7f8
-- title:
--   Integer Torus Map: real right inverse
-- statement:
--   Cast an actual rational right-inverse identity to the reals. This avoids
--   assuming that arbitrary rationally independent real vectors are real-independent.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L60-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L60-L70

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

theorem DeletionCode.IntegerTorusMap.real_right_inverse [DecidableEq J] (A : Matrix J I ℚ)
    (h : LinearIndependent ℚ A.row) :
    ∃ B : Matrix I J ℝ, A.map (Rat.castHom ℝ) * B = 1 := by sorry
