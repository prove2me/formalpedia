-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSupport_connected_block_nonzero
-- name    : DeletionCode.RelationBlockSupport.connected_block_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:13:43.231314+00:00
-- url     : https://prove2.me/theorems/e223350f-6169-4525-b734-34bf2dd3bba9
-- title:
--   Relation Block Support: connected block nonzero
-- statement:
--   Each actual EqvGen adjacency block meeting the nonzero coefficient support
--   meets the nonzero support of w at a gram of a rule in that same block.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L101-L119
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L101-L119

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSupport.connected_block_nonzero {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (b : I)
    (hactive : ∃ i, Connected G b i ∧ a i ≠ 0) :
    ∃ g i, Connected G b i ∧ G i g ≠ 0 ∧ w g ≠ 0 := by sorry
