-- Prove2me | Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_surjective
-- name    : DeletionCode.IntegerTorusMap.jointHash_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:36:07.645437+00:00
-- url     : https://prove2.me/theorems/7f501eb3-881e-4f65-a1ce-fe0e36b8cd4d
-- title:
--   Integer Torus Map: joint Hash surjective
-- statement:
--   Rationally independent integer rule vectors give a surjective joint torus
--   hash, with no additional rank or torus-surjectivity premise.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L93-L104
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L93-L104

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

theorem DeletionCode.IntegerTorusMap.jointHash_surjective (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j => fun i => (w j i : ℚ))) :
    Function.Surjective (jointHash w) := by sorry
