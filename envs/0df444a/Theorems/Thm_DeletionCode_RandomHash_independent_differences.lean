-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_independent_differences
-- name    : DeletionCode.RandomHash.independent_differences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:14.272053+00:00
-- url     : https://prove2.me/theorems/a3d52944-d341-4982-bfd2-fdf3f8fd4689
-- title:
--   Random Hash: independent differences
-- statement:
--   The full joint-law assertion of `lem:hash-independent`, for the actual
--   real-weight probability space specified by the manuscript.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L99-L104
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L99-L104

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.independent_differences (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => realWeightedHash weights (w j)) (realWeights I) ∧
    (∀ j, MeasurePreserving (fun weights => realWeightedHash weights (w j)) (realWeights I) volume) ∧
    MeasurePreserving (fun weights j => realWeightedHash weights (w j)) (realWeights I) volume := by sorry
