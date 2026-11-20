-- Prove2me | Theorems.Thm_DeletionCode_SignedRuleCount_generatingRuleSet_card_le_data
-- name    : DeletionCode.SignedRuleCount.generatingRuleSet_card_le_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:19.519647+00:00
-- url     : https://prove2.me/theorems/5e0cbd5e-795a-4eb6-8cbe-9a59b7e854a5
-- title:
--   Signed Rule Count: generating Rule Set card le data
-- statement:
--   The Signed Rule Count construction uses the generating Rule Set card le data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean#L70-L77
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean#L70-L77

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Definitions.Def_DeletionCode_SignedRuleCount
set_option autoImplicit true
open DeletionCode DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount

theorem DeletionCode.SignedRuleCount.generatingRuleSet_card_le_data (x : Letters) (n k ν R c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} ≤
      Nat.card {data : RecoveredData ν // GeneratingData x n k ν c data} := by sorry
