-- Prove2me | Theorems.Thm_DeletionCode_BlockAdjunction_new_block_component_bound
-- name    : DeletionCode.BlockAdjunction.new_block_component_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:10.056482+00:00
-- url     : https://prove2.me/theorems/8074ea49-355c-4aa7-9df5-230d1999e42c
-- title:
--   Block Adjunction: new block component bound
-- statement:
--   The actual new block also satisfies the connected-block component bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L152-L164
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L152-L164

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition

theorem DeletionCode.BlockAdjunction.new_block_component_bound {t k : ℕ} (ht : 1 ≤ t) (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hcatalogue : ∀ u ∈ U, CatalogueRule t k u) :
    componentCount (blockOf (insert w U) w) ≤
      (2 * t - 1) * (blockOf (insert w U) w).card + 1 := by sorry
