-- Prove2me | Theorems.Thm_DeletionCode_AttachedBlocks_attached_block_count_le_vertices
-- name    : DeletionCode.AttachedBlocks.attached_block_count_le_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:20.224681+00:00
-- url     : https://prove2.me/theorems/19a470f6-fca8-44b6-a8f6-d013d1e92fe9
-- title:
--   Attached Blocks: attached block count le vertices
-- statement:
--   Different attached blocks must use different vertices of the new rule.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AttachedBlocks.lean#L18-L41
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/AttachedBlocks.lean#L18-L41

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SignedRuleCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_AttachedBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.AttachedBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open scoped BigOperators

theorem DeletionCode.AttachedBlocks.attached_block_count_le_vertices {k : ℕ}
    (Bs : Finset (RuleSet k)) (w : Gram (windowLength k) → ℤ)
    (hmeet : ∀ B ∈ Bs, ∃ v, Incident B v ∧ Incident {w} v)
    (hdisjoint : ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v) :
    Bs.card ≤ Fintype.card (RuleSetVertex {w}) := by sorry
