-- Prove2me | Theorems.Thm_DeletionCode_BlockAdjunction_new_block_card_bound
-- name    : DeletionCode.BlockAdjunction.new_block_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:21:16.205057+00:00
-- url     : https://prove2.me/theorems/b87e3d7c-89d4-4168-bca5-db648078e790
-- title:
--   Block Adjunction: new block card bound
-- statement:
--   The size estimate for the actual newly formed block of a catalogue rule.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L143-L149
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L143-L149

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition

theorem DeletionCode.BlockAdjunction.new_block_card_bound {t k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hsize : ∀ B ∈ blocks U, B.card ≤ windowLength k) :
    (blockOf (insert w U) w).card ≤ 1 + 4 * t * (windowLength k) ^ 2 := by sorry
