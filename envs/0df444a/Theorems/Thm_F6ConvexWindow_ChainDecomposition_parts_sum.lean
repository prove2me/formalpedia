-- Prove2me | Theorems.Thm_F6ConvexWindow_ChainDecomposition_parts_sum
-- name    : F6ConvexWindow.ChainDecomposition.parts_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:08:46.876949+00:00
-- url     : https://prove2.me/theorems/2d65daf8-9358-5acb-b8d2-9bda21be81c6
-- title:
--   Chain Decomposition: parts sum
-- statement:
--   The Chain Decomposition construction uses the parts sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L561-L562
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L561-L562

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

theorem F6ConvexWindow.ChainDecomposition.parts_sum (f : V → ℕ) : (∑ i, ∑ x ∈ d.part i, f x) = ∑ x, f x := by sorry
