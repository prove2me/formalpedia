-- Prove2me | Theorems.Thm_DeletionCode_FiniteGenerating_generating_blockOf
-- name    : DeletionCode.FiniteGenerating.generating_blockOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:48.22332+00:00
-- url     : https://prove2.me/theorems/d223e0fe-0fbd-4eba-a964-7c2a29b5a4dd
-- title:
--   Finite Generating: generating block Of
-- statement:
--   The Finite Generating construction uses the generating block Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L76-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L76-L82

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

theorem DeletionCode.FiniteGenerating.generating_blockOf {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G : RuleSet k} (hgen : GeneratingAt v G) (a : Gram (windowLength k) → ℤ) :
    GeneratingAt v (blockOf G a) := by sorry
