-- Prove2me | Theorems.Thm_F6ConvexWindow_triplesDescending_strict
-- name    : F6ConvexWindow.triplesDescending_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:19:25.85377+00:00
-- url     : https://prove2.me/theorems/7f9fff69-ff68-400e-9a15-294d652ce7c5
-- title:
--   F6 Convex Window: triples Descending strict
-- statement:
--   The F6 Convex Window construction uses the triples Descending strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L237-L260
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L237-L260

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triplesDescending_strict (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) :
    (triplesDescending F).Pairwise (fun T S => ideal S ⊂ ideal T) := by sorry
