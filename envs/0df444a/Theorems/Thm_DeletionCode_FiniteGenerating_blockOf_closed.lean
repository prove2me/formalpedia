-- Prove2me | Theorems.Thm_DeletionCode_FiniteGenerating_blockOf_closed
-- name    : DeletionCode.FiniteGenerating.blockOf_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:26.593305+00:00
-- url     : https://prove2.me/theorems/fae487fb-6233-4997-9c2d-d3bb6f9a55e2
-- title:
--   Finite Generating: block Of closed
-- statement:
--   The Finite Generating construction uses the block Of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L70-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L70-L74

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

theorem DeletionCode.FiniteGenerating.blockOf_closed {k : ℕ} (G : RuleSet k) (a : Gram (windowLength k) → ℤ) :
    ClosedIn G (blockOf G a) := by sorry
