-- Prove2me | Theorems.Thm_F6ConvexWindow_ChainDecomposition_parts_card
-- name    : F6ConvexWindow.ChainDecomposition.parts_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:36:19.740199+00:00
-- url     : https://prove2.me/theorems/8a21f5f0-e060-50ba-9cdc-0f2e09e9846c
-- title:
--   Chain Decomposition: parts card
-- statement:
--   The Chain Decomposition construction uses the parts card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L556-L559
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L556-L559

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
open F6ConvexWindow.ChainDecomposition
variable {k : ℕ} (d : ChainDecomposition (V := V) k)

theorem F6ConvexWindow.ChainDecomposition.parts_card : (∑ i, (d.part i).card) = Fintype.card V := by sorry
