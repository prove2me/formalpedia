-- Prove2me | Theorems.Thm_F6ConvexWindow_no_reentry
-- name    : F6ConvexWindow.no_reentry
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:33:50.445423+00:00
-- url     : https://prove2.me/theorems/0b757f56-e103-59e8-b821-829d5615b022
-- title:
--   F6 Convex Window: no reentry
-- statement:
--   §7d: an element cannot leave and later reenter nested generated ideals.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L87-L94
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L87-L94

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.no_reentry {s t u : Finset V} (hu : Antichain u)
    (hst : ideal s ⊆ ideal t) (htu : ideal t ⊆ ideal u)
    {x : V} (hxs : x ∈ s) (hxu : x ∈ u) : x ∈ t := by sorry
