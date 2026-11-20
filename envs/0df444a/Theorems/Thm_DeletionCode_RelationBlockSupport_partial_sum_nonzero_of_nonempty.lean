-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSupport_partial_sum_nonzero_of_nonempty
-- name    : DeletionCode.RelationBlockSupport.partial_sum_nonzero_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:26.162179+00:00
-- url     : https://prove2.me/theorems/37861f89-93ff-4059-9a1f-aa0706ab8eeb
-- title:
--   Relation Block Support: partial sum nonzero of nonempty
-- statement:
--   The commonly used nonempty, everywhere nonzero coefficient version.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L33-L38
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L33-L38

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSupport.partial_sum_nonzero_of_nonempty {I H : Type*} (G : I → H → ℚ)
    (hG : LinearIndependent ℚ G) (T : Finset I) (a : I → ℚ)
    (hT : T.Nonempty) (ha : ∀ i ∈ T, a i ≠ 0) :
    ∃ g, (∑ i ∈ T, a i * G i g) ≠ 0 := by sorry
