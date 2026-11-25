-- Prove2me | Theorems.Thm_F6ConvexWindow_mem_tripleFamily
-- name    : F6ConvexWindow.mem_tripleFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:32:33.673127+00:00
-- url     : https://prove2.me/theorems/a7c958f9-db61-458d-a7d2-cb105a83f991
-- title:
--   F6 Convex Window: mem triple Family
-- statement:
--   The F6 Convex Window construction uses the mem triple Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L21-L22
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L21-L22

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.mem_tripleFamily {T : Finset V} :
    T ∈ tripleFamily ↔ IsTriple T := by sorry
