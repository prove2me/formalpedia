-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSupport_partial_sum_nonzero
-- name    : DeletionCode.RelationBlockSupport.partial_sum_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:12.541611+00:00
-- url     : https://prove2.me/theorems/81ddfabc-4fc8-4afb-8f11-d04ecdedbec2
-- title:
--   Relation Block Support: partial sum nonzero
-- statement:
--   A finite partial combination of independent rational vectors with at least
--   one nonzero coefficient has an actual nonzero coordinate.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L18-L30
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L18-L30

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSupport.partial_sum_nonzero {I H : Type*} (G : I → H → ℚ)
    (hG : LinearIndependent ℚ G) (T : Finset I) (a : I → ℚ)
    (hactive : ∃ i ∈ T, a i ≠ 0) :
    ∃ g, (∑ i ∈ T, a i * G i g) ≠ 0 := by sorry
