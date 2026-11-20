-- Prove2me | Theorems.Thm_DeletionCode_RuleReconstruction_negativeLetters_agree
-- name    : DeletionCode.RuleReconstruction.negativeLetters_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:18:49.435772+00:00
-- url     : https://prove2.me/theorems/abd1621c-3ec7-49f7-b4c6-00fc60dafe85
-- title:
--   Rule Reconstruction: negative Letters agree
-- statement:
--   The Rule Reconstruction construction uses the negative Letters agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L23-L27
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L23-L27

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators

theorem DeletionCode.RuleReconstruction.negativeLetters_agree {ν k : ℕ} (E : EditedFamily (Fin ν) k) (b : Fin ν) :
    Agree (negativeLetters (dataOfFamily E) b) 0
      (negativePath k (E.header b) (E.long b)) 0 (negativeLength k (E.header b)) := by sorry
