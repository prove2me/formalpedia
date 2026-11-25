-- Prove2me | Theorems.Thm_DilworthTheorem_antichain_subset_lowerCone
-- name    : DilworthTheorem.antichain_subset_lowerCone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:54:15.832918+00:00
-- url     : https://prove2.me/theorems/068cf847-c6a7-4fff-bc99-b171e43a3c4a
-- title:
--   Dilworth Theorem: antichain subset lower Cone
-- statement:
--   The Dilworth Theorem construction uses the antichain subset lower Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L144-L145
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L144-L145

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

theorem DilworthTheorem.antichain_subset_lowerCone {S A : Finset α} (hAS : A ⊆ S) : A ⊆ lowerCone S A := by sorry
