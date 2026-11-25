-- Prove2me | Theorems.Thm_DilworthTheorem_cmax_not_mem_lowerCone
-- name    : DilworthTheorem.cmax_not_mem_lowerCone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:54:42.021798+00:00
-- url     : https://prove2.me/theorems/51bc92b6-ee4b-5e6a-9c50-88ff6b48ef89
-- title:
--   Dilworth Theorem: cmax not mem lower Cone
-- statement:
--   The Dilworth Theorem construction uses the cmax not mem lower Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L176-L181
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L176-L181

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

theorem DilworthTheorem.cmax_not_mem_lowerCone {S A C : Finset α} {cmax : α}
    (hAS : A ⊆ S) (hcmax_in : cmax ∈ C) (hcmax_max : ∀ x ∈ S, cmax ≤ x → x = cmax)
    (hAC_disj : Disjoint A C) :
    cmax ∉ lowerCone S A := by sorry
