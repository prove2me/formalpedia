-- Prove2me | Theorems.Thm_F6ConvexWindow_two_chain_degree_eq_A2
-- name    : F6ConvexWindow.two_chain_degree_eq_A2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:10:48.849856+00:00
-- url     : https://prove2.me/theorems/51370ace-dba0-44e6-a05d-c389f5a32bdf
-- title:
--   F6 Convex Window: two chain degree eq A2
-- statement:
--   For two chains, each row counts every two-element antichain exactly once.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L631-L661
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L631-L661

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.two_chain_degree_eq_A2 (d : ChainDecomposition (V := V) 2) (i : Fin 2) :
    (∑ x ∈ d.part i, (Inc x).card) = Ak (V := V) 2 := by sorry
