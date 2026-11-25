-- Prove2me | Theorems.Thm_F6ConvexWindow_mem_tripleUnion
-- name    : F6ConvexWindow.mem_tripleUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:32:08.207802+00:00
-- url     : https://prove2.me/theorems/108a22f2-a935-449c-9195-23a89a4c66a9
-- title:
--   F6 Convex Window: mem triple Union
-- statement:
--   The F6 Convex Window construction uses the mem triple Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L28-L29
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L28-L29

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.mem_tripleUnion {F : Finset (Finset V)} {x : V} :
    x ∈ tripleUnion F ↔ ∃ T ∈ F, x ∈ T := by sorry
