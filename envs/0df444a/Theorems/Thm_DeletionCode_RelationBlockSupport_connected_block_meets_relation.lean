-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSupport_connected_block_meets_relation
-- name    : DeletionCode.RelationBlockSupport.connected_block_meets_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:25.79418+00:00
-- url     : https://prove2.me/theorems/6bec329b-76e3-4842-a6ee-b53da1ed5280
-- title:
--   Relation Block Support: connected block meets relation
-- statement:
--   The surviving gram provides an actual incident support vertex shared with
--   w, ready for the block/component counting step.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L123-L131
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L123-L131

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSupport.connected_block_meets_relation {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (b : I)
    (hactive : ∃ i, Connected G b i ∧ a i ≠ 0) :
    ∃ i, Connected G b i ∧ ∃ v, Incident {G i} v ∧ Incident {w} v := by sorry
