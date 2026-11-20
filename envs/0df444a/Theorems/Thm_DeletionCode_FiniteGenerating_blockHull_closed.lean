-- Prove2me | Theorems.Thm_DeletionCode_FiniteGenerating_blockHull_closed
-- name    : DeletionCode.FiniteGenerating.blockHull_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:55.642437+00:00
-- url     : https://prove2.me/theorems/e5e4c2b2-99a5-46db-ac91-14a5e1ce9c2b
-- title:
--   Finite Generating: block Hull closed
-- statement:
--   The Finite Generating construction uses the block Hull closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L60-L63
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L60-L63

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_GeneratingBlocks_blockHull_closed
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_closed

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

theorem DeletionCode.FiniteGenerating.blockHull_closed {k : ℕ} (G I : RuleSet k) :
    ClosedIn G (RelationBlockSavings.blockHull G I) := by sorry
