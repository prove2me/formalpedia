-- Prove2me | Theorems.Thm_DeletionCode_SignedRuleCount_rulesOf_chosenData
-- name    : DeletionCode.SignedRuleCount.rulesOf_chosenData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:04.539664+00:00
-- url     : https://prove2.me/theorems/ec663af3-3c70-4918-93bc-84d11358bd32
-- title:
--   Signed Rule Count: rules Of chosen Data
-- statement:
--   The Signed Rule Count construction uses the rules Of chosen Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean#L44-L47
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean#L44-L47

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Definitions.Def_DeletionCode_SignedRuleCount
set_option autoImplicit true
open DeletionCode DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount

theorem DeletionCode.SignedRuleCount.rulesOf_chosenData (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (Q : {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q}) :
    rulesOfData k group (chooseRuleData x n k ν R c group Q).val = Q.val := by sorry
