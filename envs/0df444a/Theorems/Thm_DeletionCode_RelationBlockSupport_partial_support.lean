-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSupport_partial_support
-- name    : DeletionCode.RelationBlockSupport.partial_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:13:29.419825+00:00
-- url     : https://prove2.me/theorems/44636378-1323-4731-ad24-f69c8b8e5259
-- title:
--   Relation Block Support: partial support
-- statement:
--   Every nonzero partial coordinate is supported by an actual selected rule.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L55-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L55-L65

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSupport.partial_support {I : Type*} {L : ℕ}
    (G : I → Gram L → ℤ) (T : Finset I) (a : I → ℚ) (g : Gram L)
    (hne : (∑ i ∈ T, a i * (G i g : ℚ)) ≠ 0) :
    ∃ i ∈ T, G i g ≠ 0 := by sorry
