-- Prove2me | Theorems.Thm_DeletionCode_GeneratingBlocks_supplier_connected
-- name    : DeletionCode.GeneratingBlocks.supplier_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:05.132427+00:00
-- url     : https://prove2.me/theorems/41852bf2-ac80-456f-b972-88a9353a6707
-- title:
--   Generating Blocks: supplier connected
-- statement:
--   A supplying rule is in the same block, derived from the shared gram.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L43-L47
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingBlocks.lean#L43-L47

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph

theorem DeletionCode.GeneratingBlocks.supplier_connected {I : Type*} {L : ℕ} (G : I → Gram L → ℤ)
    (i j : I) (g : Gram L) (hi : G i g = -1) (hj : G j g ≠ 0) :
    Connected G i j := by sorry
