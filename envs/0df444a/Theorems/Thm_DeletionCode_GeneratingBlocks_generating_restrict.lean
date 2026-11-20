-- Prove2me | Theorems.Thm_DeletionCode_GeneratingBlocks_generating_restrict
-- name    : DeletionCode.GeneratingBlocks.generating_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:09:20.914141+00:00
-- url     : https://prove2.me/theorems/e9a4ee01-61ac-4c2b-adfc-e2bc7d31725a
-- title:
--   Generating Blocks: generating restrict
-- statement:
--   Keeping whole blocks retains every required earlier supplier.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L50-L58
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L50-L58

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph

theorem DeletionCode.GeneratingBlocks.generating_restrict {I : Type*} {L : ℕ} (v : Gram L → ℤ)
    (G : I → Gram L → ℤ) (rank : I → ℕ) (S : Set I)
    (hgen : Generating v G rank) (hclosed : BlockClosed G S) :
    Generating v (fun i : S => G i.val) (fun i : S => rank i.val) := by sorry
