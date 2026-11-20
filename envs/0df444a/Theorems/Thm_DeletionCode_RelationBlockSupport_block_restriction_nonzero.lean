-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSupport_block_restriction_nonzero
-- name    : DeletionCode.RelationBlockSupport.block_restriction_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:10:59.329786+00:00
-- url     : https://prove2.me/theorems/389e0775-970e-4dfc-b49f-6dc8b53f0615
-- title:
--   Relation Block Support: block restriction nonzero
-- statement:
--   A block restriction containing an active coefficient has a nonzero actual
--   gram that survives in w. Whole-block closure supplies the separation premise.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L82-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L82-L97

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSupport.block_restriction_nonzero {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (T : Finset I)
    (hactive : ∃ i ∈ T, a i ≠ 0)
    (hclosed : BlockClosed G (↑T : Set I)) :
    ∃ g, w g ≠ 0 ∧ ∃ i ∈ T, G i g ≠ 0 := by sorry
