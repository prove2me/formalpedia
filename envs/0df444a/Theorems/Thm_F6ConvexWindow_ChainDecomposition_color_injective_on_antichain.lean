-- Prove2me | Theorems.Thm_F6ConvexWindow_ChainDecomposition_color_injective_on_antichain
-- name    : F6ConvexWindow.ChainDecomposition.color_injective_on_antichain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:36:38.651464+00:00
-- url     : https://prove2.me/theorems/ec27d0fd-c5ff-4a00-97af-71cfd389e2ef
-- title:
--   Chain Decomposition: color injective on antichain
-- statement:
--   The Chain Decomposition construction uses the color injective on antichain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L564-L570
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L564-L570

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

theorem F6ConvexWindow.ChainDecomposition.color_injective_on_antichain {T : Finset V} (ht : Antichain T) :
    Set.InjOn d.color T := by sorry
