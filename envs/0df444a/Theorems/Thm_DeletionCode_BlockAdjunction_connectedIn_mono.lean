-- Prove2me | Theorems.Thm_DeletionCode_BlockAdjunction_connectedIn_mono
-- name    : DeletionCode.BlockAdjunction.connectedIn_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:56.404982+00:00
-- url     : https://prove2.me/theorems/fbbf3df8-ecc5-412d-9549-6fe4aa9b1053
-- title:
--   Block Adjunction: connected In mono
-- statement:
--   The Block Adjunction construction uses the connected In mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L15-L22
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BlockAdjunction.lean#L15-L22

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition

theorem DeletionCode.BlockAdjunction.connectedIn_mono {k : ℕ} {U V : RuleSet k} (hUV : U ⊆ V)
    {a b : Gram (windowLength k) → ℤ} (h : ConnectedIn U a b) : ConnectedIn V a b := by sorry
