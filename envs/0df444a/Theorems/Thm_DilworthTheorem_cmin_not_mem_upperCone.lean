-- Prove2me | Theorems.Thm_DilworthTheorem_cmin_not_mem_upperCone
-- name    : DilworthTheorem.cmin_not_mem_upperCone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:54:46.537295+00:00
-- url     : https://prove2.me/theorems/b05d1e01-7cfc-5ee2-9ce9-710a9676a8a9
-- title:
--   Dilworth Theorem: cmin not mem upper Cone
-- statement:
--   The Dilworth Theorem construction uses the cmin not mem upper Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L183-L188
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L183-L188

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Antichain
import Mathlib.Tactic
import Definitions.Def_StableMarriageF6_DilworthTheorem
set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]

theorem DilworthTheorem.cmin_not_mem_upperCone {S A C : Finset α} {cmin : α}
    (hAS : A ⊆ S) (hcmin_in : cmin ∈ C) (hcmin_min : ∀ x ∈ S, x ≤ cmin → x = cmin)
    (hAC_disj : Disjoint A C) :
    cmin ∉ upperCone S A := by sorry
