-- Prove2me | Theorems.Thm_DeletionCode_IntegerTorusMap_continuous_jointHash
-- name    : DeletionCode.IntegerTorusMap.continuous_jointHash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:36:05.060848+00:00
-- url     : https://prove2.me/theorems/bda34ac6-1692-4193-843a-3db424b778e4
-- title:
--   Integer Torus Map: continuous joint Hash
-- statement:
--   The Integer Torus Map construction uses the continuous joint Hash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L36-L40
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/IntegerTorusMap.lean#L36-L40

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

theorem DeletionCode.IntegerTorusMap.continuous_jointHash (w : J → I → ℤ) : Continuous (jointHash w) := by sorry
