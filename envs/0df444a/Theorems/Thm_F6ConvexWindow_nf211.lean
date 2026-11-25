-- Prove2me | Theorems.Thm_F6ConvexWindow_nf211
-- name    : F6ConvexWindow.nf211
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:39:42.358802+00:00
-- url     : https://prove2.me/theorems/1b1ac711-e73e-57d6-ac5b-3af507b6cc5f
-- title:
--   F6 Convex Window: nf211
-- statement:
--   CI2 excludes the induced 2+1+1 configuration used in §7a.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L106-L112
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L106-L112

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.nf211 (hci : CI2 (V := V)) {x y a b : V} (hxy : x < y)
    (hxa : IncRel x a) (hya : IncRel y a)
    (hxb : IncRel x b) (hyb : IncRel y b) (hab : IncRel a b) : False := by sorry
