-- Prove2me | Theorems.Thm_DeletionCode_RelationSupport_support_inclusion
-- name    : DeletionCode.RelationSupport.support_inclusion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:12:55.750061+00:00
-- url     : https://prove2.me/theorems/f0f73278-16bb-4585-a525-c71e11f97d3b
-- title:
--   Relation Support: support inclusion
-- statement:
--   The Relation Support construction uses the support inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSupport.lean#L18-L30
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationSupport.lean#L18-L30

import Definitions.Def_DeletionCode_WitnessAlgebra
import Definitions.Def_DeletionCode_RelationSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationSupport
open SignedSupport
open scoped BigOperators

theorem DeletionCode.RelationSupport.support_inclusion {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : Relation G w a) (g : Gram L) (hw : w g ≠ 0) :
    ∃ i, G i g ≠ 0 := by sorry
