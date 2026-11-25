-- Prove2me | Theorems.Thm_F6ConvexWindow_union_card_step
-- name    : F6ConvexWindow.union_card_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:22:16.981798+00:00
-- url     : https://prove2.me/theorems/26807e8d-4f85-435e-8c16-f8ab514d4242
-- title:
--   F6 Convex Window: union card step
-- statement:
--   Exact union growth, with the empty-transition indicator displayed.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L497-L509
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L497-L509

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.union_card_step {U T : Finset V} (ht : T.card = 3) (hi : (U ∩ T).card ≤ 1) :
    (U ∪ T).card = U.card + 2 + if Disjoint U T then 1 else 0 := by sorry
