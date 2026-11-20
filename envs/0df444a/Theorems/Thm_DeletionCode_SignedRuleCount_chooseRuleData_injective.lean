-- Prove2me | Theorems.Thm_DeletionCode_SignedRuleCount_chooseRuleData_injective
-- name    : DeletionCode.SignedRuleCount.chooseRuleData_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:13.11644+00:00
-- url     : https://prove2.me/theorems/cb7a154e-c5f7-4d8f-8484-acc4b053c4d0
-- title:
--   Signed Rule Count: choose Rule Data injective
-- statement:
--   Deterministic rule reconstruction makes the chosen preimage assignment injective.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean#L50-L60
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean#L50-L60

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Definitions.Def_DeletionCode_SignedRuleCount
set_option autoImplicit true
open DeletionCode DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount

theorem DeletionCode.SignedRuleCount.chooseRuleData_injective (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R) :
    Function.Injective (chooseRuleData x n k ν R c group) := by sorry
