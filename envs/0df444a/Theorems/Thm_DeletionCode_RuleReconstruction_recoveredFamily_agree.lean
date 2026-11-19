-- Prove2me | Theorems.Thm_DeletionCode_RuleReconstruction_recoveredFamily_agree
-- name    : DeletionCode.RuleReconstruction.recoveredFamily_agree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:18:52.076112+00:00
-- url     : https://prove2.me/theorems/8d6f4283-01de-4846-a0bf-e100ac8b7e80
-- title:
--   Rule Reconstruction: recovered Family agree
-- statement:
--   The Rule Reconstruction construction uses the recovered Family agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L29-L39
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L29-L39

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators

theorem DeletionCode.RuleReconstruction.recoveredFamily_agree {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (b : Fin ν) (side : Bool) :
    Agree ((recoveredFamily k rank (dataOfFamily E)).path b side) 0
      (E.family.path b side) 0 (windowLength k + E.family.extra b side) := by sorry
