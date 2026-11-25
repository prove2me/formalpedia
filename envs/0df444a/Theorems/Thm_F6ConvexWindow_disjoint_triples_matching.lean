-- Prove2me | Theorems.Thm_F6ConvexWindow_disjoint_triples_matching
-- name    : F6ConvexWindow.disjoint_triples_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:18:41.006041+00:00
-- url     : https://prove2.me/theorems/914d7a8e-8198-569f-bda9-d1be5cd1fa9d
-- title:
--   F6 Convex Window: disjoint triples matching
-- statement:
--   §3, empty transition: each row and each column has at most one cross neighbor.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L188-L198
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L188-L198

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.disjoint_triples_matching (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T) (hd : Disjoint S T) :
    (∀ x ∈ S, (T.filter (IncRel x)).card ≤ 1) ∧
    (∀ y ∈ T, (S.filter (IncRel y)).card ≤ 1) := by sorry
