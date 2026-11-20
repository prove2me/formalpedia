-- Prove2me | Theorems.Thm_DeletionCode_FiniteGenerating_generating_blockHull
-- name    : DeletionCode.FiniteGenerating.generating_blockHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:33.995339+00:00
-- url     : https://prove2.me/theorems/ac2009c3-3c2a-4d9c-8490-e6b4728196cf
-- title:
--   Finite Generating: generating block Hull
-- statement:
--   The Finite Generating construction uses the generating block Hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L65-L68
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L65-L68

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_GeneratingBlocks_generating_blockHull

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

theorem DeletionCode.FiniteGenerating.generating_blockHull {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G : RuleSet k} (hgen : GeneratingAt v G) (I : RuleSet k) :
    GeneratingAt v (RelationBlockSavings.blockHull G I) := by sorry
