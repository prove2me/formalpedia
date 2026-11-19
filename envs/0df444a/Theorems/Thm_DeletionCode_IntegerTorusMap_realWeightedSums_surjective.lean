-- Prove2me | Theorems.Thm_DeletionCode_IntegerTorusMap_realWeightedSums_surjective
-- name    : DeletionCode.IntegerTorusMap.realWeightedSums_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:42:22.794707+00:00
-- url     : https://prove2.me/theorems/e5062717-d5a2-4987-b122-68deef2e4993
-- title:
--   Integer Torus Map: real Weighted Sums surjective
-- statement:
--   Simultaneous real weighted sums attain every real vector.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L73-L89
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L73-L89

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

theorem DeletionCode.IntegerTorusMap.realWeightedSums_surjective (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j => fun i => (w j i : ℚ))) :
    Function.Surjective (fun weights : I → ℝ =>
      fun j => ∑ i, weights i * (w j i : ℝ)) := by sorry
