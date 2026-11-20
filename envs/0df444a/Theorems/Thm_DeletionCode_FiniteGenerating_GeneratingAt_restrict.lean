-- Prove2me | Theorems.Thm_DeletionCode_FiniteGenerating_GeneratingAt_restrict
-- name    : DeletionCode.FiniteGenerating.GeneratingAt.restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:52.708032+00:00
-- url     : https://prove2.me/theorems/9a2406ac-1b6a-4323-9672-7d36d29c2d8a
-- title:
--   Generating At: restrict
-- statement:
--   The Generating At construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L51-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L51-L58

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

theorem DeletionCode.FiniteGenerating.GeneratingAt.restrict {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G U : RuleSet k} (hgen : GeneratingAt v G) (hUG : U ⊆ G)
    (hclosed : ClosedIn G U) : GeneratingAt v U := by sorry
