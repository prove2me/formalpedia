-- Prove2me | Theorems.Thm_F6ConvexWindow_split_monotone
-- name    : F6ConvexWindow.split_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:02:17.565771+00:00
-- url     : https://prove2.me/theorems/20327cef-3898-4687-a2f5-9322aab281ad
-- title:
--   F6 Convex Window: split monotone
-- statement:
--   §4: the Above triples form an initial segment and Below triples a final segment.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L315-L327
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L315-L327

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.split_monotone (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) {x : V} (hxS : x ∉ S) (hxT : x ∉ T) :
    (Above T x → Above S x) ∧ (Below S x → Below T x) := by sorry
