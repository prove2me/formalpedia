-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_coordinate_uniform
-- name    : DeletionCode.RandomHash.coordinate_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:13.386024+00:00
-- url     : https://prove2.me/theorems/dde70460-723f-499c-87a2-7c59618c7dac
-- title:
--   Random Hash: coordinate uniform
-- statement:
--   The Random Hash construction uses the coordinate uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L25-L29
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L25-L29

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.coordinate_uniform (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (j : J) :
    MeasurePreserving (fun weights => weightedHash weights (w j)) volume volume := by sorry
