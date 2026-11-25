-- Prove2me | Theorems.Thm_DilworthTheorem_lowerCone_card_lt
-- name    : DilworthTheorem.lowerCone_card_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:55:24.673894+00:00
-- url     : https://prove2.me/theorems/20e936ab-13b0-40f1-b967-81dfcb9946bd
-- title:
--   Dilworth Theorem: lower Cone card lt
-- statement:
--   The Dilworth Theorem construction uses the lower Cone card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L190-L197
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L190-L197

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

theorem DilworthTheorem.lowerCone_card_lt {S A C : Finset α} {cmax : α}
    (hAS : A ⊆ S) (hCS : C ⊆ S) (hcmax_in : cmax ∈ C)
    (hcmax_max : ∀ x ∈ S, cmax ≤ x → x = cmax)
    (hAC_disj : Disjoint A C) :
    (lowerCone S A).card < S.card := by sorry
