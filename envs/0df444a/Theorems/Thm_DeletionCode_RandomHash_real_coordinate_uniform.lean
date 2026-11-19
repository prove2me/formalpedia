-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_real_coordinate_uniform
-- name    : DeletionCode.RandomHash.real_coordinate_uniform
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:43:17.720224+00:00
-- url     : https://prove2.me/theorems/ea5cd476-418a-429b-a13f-3981ef3485bd
-- title:
--   Random Hash: real coordinate uniform
-- statement:
--   The Random Hash construction uses the real coordinate uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L87-L90
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L87-L90

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.real_coordinate_uniform (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (j : J) :
    MeasurePreserving (fun weights => realWeightedHash weights (w j)) (realWeights I) volume := by sorry
