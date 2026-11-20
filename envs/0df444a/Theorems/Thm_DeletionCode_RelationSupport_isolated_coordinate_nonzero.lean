-- Prove2me | Theorems.Thm_DeletionCode_RelationSupport_isolated_coordinate_nonzero
-- name    : DeletionCode.RelationSupport.isolated_coordinate_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:12:58.324188+00:00
-- url     : https://prove2.me/theorems/44710388-aea0-4a5f-b78a-0001589539e8
-- title:
--   Relation Support: isolated coordinate nonzero
-- statement:
--   The Relation Support construction uses the isolated coordinate nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSupport.lean#L32-L49
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSupport.lean#L32-L49

import Definitions.Def_DeletionCode_WitnessAlgebra
import Definitions.Def_DeletionCode_RelationSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationSupport
open SignedSupport
open scoped BigOperators

theorem DeletionCode.RelationSupport.isolated_coordinate_nonzero {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : Relation G w a) (i : I) (g : Gram L)
    (ha : a i ≠ 0) (hgi : G i g ≠ 0)
    (hother : ∀ j, j ≠ i → G j g = 0) : w g ≠ 0 := by sorry
