-- Prove2me | Theorems.Thm_DeletionCode_SignedRuleCount_generatingRuleSet_finite
-- name    : DeletionCode.SignedRuleCount.generatingRuleSet_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:10.378981+00:00
-- url     : https://prove2.me/theorems/2976c2b7-4000-4017-b925-6e2fe1cedfd0
-- title:
--   Signed Rule Count: generating Rule Set finite
-- statement:
--   The Signed Rule Count construction uses the generating Rule Set finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean#L62-L68
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedRuleCount.lean#L62-L68

import Definitions.Def_DeletionCode_RuleReconstruction
import Definitions.Def_DeletionCode_GeneratingCount
import Definitions.Def_DeletionCode_SignedRuleCount
set_option autoImplicit true
open DeletionCode DeletionCode.SignedRuleCount
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RecordSerialization GeneratingCount DescriptionCount

theorem DeletionCode.SignedRuleCount.generatingRuleSet_finite (x : Letters) (n k ν R c : ℕ) (group : Fin ν → Fin R)
    (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Finite {Q : RuleSet k // GeneratingRuleSet x n k ν R c group Q} := by sorry
