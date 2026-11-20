-- Prove2me | Theorems.Thm_DeletionCode_GeneratingBlocks_generating_blockHull
-- name    : DeletionCode.GeneratingBlocks.generating_blockHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:10:01.960939+00:00
-- url     : https://prove2.me/theorems/87a28b66-46e1-4ccf-abbb-bc9c2c4d318d
-- title:
--   Generating Blocks: generating block Hull
-- statement:
--   The precise whole-block restriction used in the relation case of the witness proof.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L75-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L75-L80

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph

theorem DeletionCode.GeneratingBlocks.generating_blockHull {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (T : Set I)
    (hgen : Generating v G rank) :
    Generating v (fun i : blockHull G T => G i.val)
      (fun i : blockHull G T => rank i.val) := by sorry
