-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_independent
-- name    : DeletionCode.RandomHash.independent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:47:50.987179+00:00
-- url     : https://prove2.me/theorems/d8443420-5829-48ad-bb19-41e1395e9551
-- title:
--   Random Hash: independent
-- statement:
--   The Random Hash construction uses the independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L31-L35
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L31-L35

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.independent (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) :
    iIndepFun (fun j weights => weightedHash weights (w j)) volume := by sorry
