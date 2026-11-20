-- Prove2me | Theorems.Thm_DeletionCode_AttachedBlocks_attached_union_card_bound
-- name    : DeletionCode.AttachedBlocks.attached_union_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:13.783829+00:00
-- url     : https://prove2.me/theorems/7b16d4f0-1381-4021-bc79-1115dab4ef06
-- title:
--   Attached Blocks: attached union card bound
-- statement:
--   If each old block has at most L rules, their attached union plus the new
--   rule has at most one plus L times the new rule's support-vertex count.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AttachedBlocks.lean#L45-L66
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AttachedBlocks.lean#L45-L66

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SignedRuleCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_AttachedBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.AttachedBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open scoped BigOperators

theorem DeletionCode.AttachedBlocks.attached_union_card_bound {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ Bs, B.card ≤ L)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v) :
    (insert w (Bs.biUnion id)).card ≤ 1 + L * Fintype.card (RuleSetVertex {w}) := by sorry
