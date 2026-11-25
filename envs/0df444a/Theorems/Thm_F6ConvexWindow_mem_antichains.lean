-- Prove2me | Theorems.Thm_F6ConvexWindow_mem_antichains
-- name    : F6ConvexWindow.mem_antichains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:12.173634+00:00
-- url     : https://prove2.me/theorems/b8184595-7046-4489-8058-3df236e63d94
-- title:
--   F6 Convex Window: mem antichains
-- statement:
--   The F6 Convex Window construction uses the mem antichains property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L49-L52
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L49-L52

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.mem_antichains {s : Finset V} :
    s ∈ antichains ↔ Antichain s := by sorry
