-- Prove2me | Theorems.Thm_DeletionCode_GeneratingBlocks_generating_single_block
-- name    : DeletionCode.GeneratingBlocks.generating_single_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:04.385108+00:00
-- url     : https://prove2.me/theorems/2aab9f0e-614c-4566-a464-0921710d5eca
-- title:
--   Generating Blocks: generating single block
-- statement:
--   Restriction to a single block is the large-block case of the same argument.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L83-L90
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L83-L90

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph

theorem DeletionCode.GeneratingBlocks.generating_single_block {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (a : I)
    (hgen : Generating v G rank) :
    Generating v (fun i : {i // Connected G a i} => G i.val)
      (fun i : {i // Connected G a i} => rank i.val) := by sorry
