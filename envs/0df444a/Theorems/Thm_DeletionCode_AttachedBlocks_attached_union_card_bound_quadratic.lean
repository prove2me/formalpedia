-- Prove2me | Theorems.Thm_DeletionCode_AttachedBlocks_attached_union_card_bound_quadratic
-- name    : DeletionCode.AttachedBlocks.attached_union_card_bound_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:31.30164+00:00
-- url     : https://prove2.me/theorems/64866dcf-0258-4652-b0a7-6aa9d9d5d532
-- title:
--   Attached Blocks: attached union card bound quadratic
-- statement:
--   The large-block quadratic size estimate from an actual support-vertex bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AttachedBlocks.lean#L69-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AttachedBlocks.lean#L69-L84

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SignedRuleCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_AttachedBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.AttachedBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open scoped BigOperators

theorem DeletionCode.AttachedBlocks.attached_union_card_bound_quadratic {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ) (t L : ℕ)
    (hsize : ∀ B ∈ Bs, B.card ≤ L)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v)
    (hvertices : Fintype.card (RuleSetVertex {w}) ≤ 4 * t * L) :
    (insert w (Bs.biUnion id)).card ≤ 1 + 4 * t * L ^ 2 := by sorry
