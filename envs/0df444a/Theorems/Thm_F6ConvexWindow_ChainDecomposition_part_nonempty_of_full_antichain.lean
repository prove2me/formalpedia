-- Prove2me | Theorems.Thm_F6ConvexWindow_ChainDecomposition_part_nonempty_of_full_antichain
-- name    : F6ConvexWindow.ChainDecomposition.part_nonempty_of_full_antichain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:09:21.086007+00:00
-- url     : https://prove2.me/theorems/9894b142-722a-4b37-9e4b-0124c511eeaa
-- title:
--   Chain Decomposition: part nonempty of full antichain
-- statement:
--   The Chain Decomposition construction uses the part nonempty of full antichain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L572-L579
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L572-L579

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

theorem F6ConvexWindow.ChainDecomposition.part_nonempty_of_full_antichain {T : Finset V}
    (ht : Antichain T) (hc : T.card = k) (i : Fin k) : (d.part i).Nonempty := by sorry
