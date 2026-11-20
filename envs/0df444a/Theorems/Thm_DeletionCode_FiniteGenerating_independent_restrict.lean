-- Prove2me | Theorems.Thm_DeletionCode_FiniteGenerating_independent_restrict
-- name    : DeletionCode.FiniteGenerating.independent_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:24:30.109919+00:00
-- url     : https://prove2.me/theorems/afad069d-d0c8-444d-aa66-59d7e0678f09
-- title:
--   Finite Generating: independent restrict
-- statement:
--   The Finite Generating construction uses the independent restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L30-L36
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteGenerating.lean#L30-L36

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition

theorem DeletionCode.FiniteGenerating.independent_restrict {k : ℕ} {G U : RuleSet k} (hUG : U ⊆ G)
    (hind : Independent G) : Independent U := by sorry
