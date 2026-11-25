-- Prove2me | Theorems.Thm_DilworthTheorem_lowerCone_union_upperCone
-- name    : DilworthTheorem.lowerCone_union_upperCone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:54:48.871712+00:00
-- url     : https://prove2.me/theorems/fda33fd6-4996-4eee-8043-13a05f475054
-- title:
--   Dilworth Theorem: lower Cone union upper Cone
-- statement:
--   The Dilworth Theorem construction uses the lower Cone union upper Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L158-L174
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L158-L174

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

theorem DilworthTheorem.lowerCone_union_upperCone (S A : Finset α) (k : ℕ)
    (hAS : A ⊆ S) (hA_anti : IsAntichain (A : Set α)) (hA_card : A.card = k)
    (h_bound : ∀ B ⊆ S, IsAntichain (B : Set α) → B.card ≤ k) :
    lowerCone S A ∪ upperCone S A = S := by sorry
