-- Prove2me | Theorems.Thm_DeletionCode_RelationBlockSupport_restriction_eq_at
-- name    : DeletionCode.RelationBlockSupport.restriction_eq_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:13:24.785631+00:00
-- url     : https://prove2.me/theorems/f534bcab-e6fb-43a4-b538-d2d86a905125
-- title:
--   Relation Block Support: restriction eq at
-- statement:
--   At a coordinate vanishing outside T, the full relation equals its actual
--   finite restriction to T.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L42-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RelationBlockSupport.lean#L42-L52

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators

theorem DeletionCode.RelationBlockSupport.restriction_eq_at {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : RelationSupport.Relation G w a) (T : Finset I) (g : Gram L)
    (houtside : ∀ i, i ∉ T → G i g = 0) :
    (w g : ℚ) = ∑ i ∈ T, a i * (G i g : ℚ) := by sorry
