-- Prove2me | Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
-- name    : F6ConvexWindow.ChainDecomposition.mem_part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:11.06764+00:00
-- url     : https://prove2.me/theorems/cc2b3ab7-eb83-5ad5-abc9-0a59b1f7e914
-- title:
--   Chain Decomposition: mem part
-- statement:
--   The Chain Decomposition construction uses the mem part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L553-L554
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L553-L554

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

theorem F6ConvexWindow.ChainDecomposition.mem_part {i : Fin k} {x : V} : x ∈ d.part i ↔ d.color x = i := by sorry
