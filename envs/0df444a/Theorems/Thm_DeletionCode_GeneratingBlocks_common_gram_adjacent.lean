-- Prove2me | Theorems.Thm_DeletionCode_GeneratingBlocks_common_gram_adjacent
-- name    : DeletionCode.GeneratingBlocks.common_gram_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:10:27.613864+00:00
-- url     : https://prove2.me/theorems/3152e267-cc18-4318-a1c8-023aaeca88dc
-- title:
--   Generating Blocks: common gram adjacent
-- statement:
--   The Generating Blocks construction uses the common gram adjacent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L37-L40
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L37-L40

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph

theorem DeletionCode.GeneratingBlocks.common_gram_adjacent {I : Type*} {L : ℕ} (G : I → Gram L → ℤ)
    (i j : I) (g : Gram L) (hi : G i g ≠ 0) (hj : G j g ≠ 0) :
    Adjacent G i j := by sorry
