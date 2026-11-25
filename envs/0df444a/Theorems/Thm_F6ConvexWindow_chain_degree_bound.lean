-- Prove2me | Theorems.Thm_F6ConvexWindow_chain_degree_bound
-- name    : F6ConvexWindow.chain_degree_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:34:46.335628+00:00
-- url     : https://prove2.me/theorems/cb4ec738-23a6-56dd-baba-8cde43411bf3
-- title:
--   F6 Convex Window: chain degree bound
-- statement:
--   §8 chain row bound, written without natural-number subtraction.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L426-L433
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L426-L433

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.chain_degree_bound (hci : CI2 (V := V)) {C : Finset V}
    (hc : Chain C) (hn : C.Nonempty) :
    (∑ x ∈ C, (Inc x).card) + 2 ≤ Fintype.card V + C.card := by sorry
