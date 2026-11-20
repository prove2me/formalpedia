-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_real_independent
-- name    : DeletionCode.RandomHash.real_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:43:24.24117+00:00
-- url     : https://prove2.me/theorems/8553950e-7415-4a29-a1aa-bb247042915c
-- title:
--   Random Hash: real independent
-- statement:
--   The Random Hash construction uses the real independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L92-L95
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L92-L95

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.real_independent (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => realWeightedHash weights (w j)) (realWeights I) := by sorry
