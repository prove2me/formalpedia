-- Prove2me | Theorems.Thm_DeletionCode_CodeExistence_labelCount_eq_scale
-- name    : DeletionCode.CodeExistence.labelCount_eq_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:08:46.865951+00:00
-- url     : https://prove2.me/theorems/fb577249-e434-40f8-8b67-9f3ffd50240d
-- title:
--   Code Existence: label Count eq scale
-- statement:
--   The chosen integer Q is exactly the required scale; no rounding loss
--   is needed because all factors in the manuscript's ceiling are integers.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean#L20-L24
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeExistence.lean#L20-L24

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
import Definitions.Def_DeletionCode_CodeExistence
set_option autoImplicit true
open DeletionCode DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection

theorem DeletionCode.CodeExistence.labelCount_eq_scale (t n : ℕ) :
    RedundancyBounds.labelCount t n =
      8 * ObstructionBound.scale t n (PaperParameters.k n) := by sorry
