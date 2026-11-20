-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSupport_outside_block_vanishes
-- name    : DeletionCode.RelationBlockSupport.outside_block_vanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:13:35.376603+00:00
-- url     : https://prove2.me/theorems/06275b36-6b1f-4717-b697-e50d60fad79f
-- title:
--   Relation Block Support: outside block vanishes
-- statement:
--   An actual gram supported in a whole adjacency block is absent from every
--   rule outside that block. The same holds for any union of whole blocks.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L69-L78
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L69-L78

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSupport.outside_block_vanishes {I : Type*} {L : ℕ}
    (G : I → Gram L → ℤ) (T : Finset I)
    (hclosed : BlockClosed G (↑T : Set I)) (g : Gram L)
    (hsupport : ∃ i ∈ T, G i g ≠ 0) :
    ∀ j, j ∉ T → G j g = 0 := by sorry
