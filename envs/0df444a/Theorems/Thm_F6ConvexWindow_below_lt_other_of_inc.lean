-- Prove2me | Theorems.Thm_F6ConvexWindow_below_lt_other_of_inc
-- name    : F6ConvexWindow.below_lt_other_of_inc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:19:13.188291+00:00
-- url     : https://prove2.me/theorems/1642fc88-dd5d-4326-862c-949b98c94f0a
-- title:
--   F6 Convex Window: below lt other of inc
-- statement:
--   A Below point incomparable with one triple member is below the other two.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L55-L69
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L55-L69

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.below_lt_other_of_inc {T : Finset V} (ht : T.card = 3)
    {x s y : V} (hx : Below T x) (hs : s ∈ T) (hy : y ∈ T)
    (hsy : s ≠ y) (hxs : IncRel x s) : x < y := by sorry
