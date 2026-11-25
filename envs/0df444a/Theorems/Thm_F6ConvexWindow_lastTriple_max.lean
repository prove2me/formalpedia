-- Prove2me | Theorems.Thm_F6ConvexWindow_lastTriple_max
-- name    : F6ConvexWindow.lastTriple_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:33:47.441407+00:00
-- url     : https://prove2.me/theorems/d06787e5-839c-45aa-afff-27c444ac0d04
-- title:
--   F6 Convex Window: last Triple max
-- statement:
--   The F6 Convex Window construction uses the last Triple max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L214-L216
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L214-L216

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.lastTriple_max (F : Finset (Finset V)) (hn : F.Nonempty) :
    ∀ S ∈ F, (ideal S).card ≤ (ideal (lastTriple F hn)).card := by sorry
