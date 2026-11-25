-- Prove2me | Theorems.Thm_F6ConvexWindow_ideal_injective
-- name    : F6ConvexWindow.ideal_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:02:15.483814+00:00
-- url     : https://prove2.me/theorems/0dd9b9e2-9e4b-4df2-8335-d54d77a009fc
-- title:
--   F6 Convex Window: ideal injective
-- statement:
--   The F6 Convex Window construction uses the ideal injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L70-L84
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L70-L84

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.ideal_injective {s t : Finset V} (hs : Antichain s) (ht : Antichain t)
    (h : ideal s = ideal t) : s = t := by sorry
