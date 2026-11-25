-- Prove2me | Theorems.Thm_DilworthTheorem_antichain_subset_upperCone
-- name    : DilworthTheorem.antichain_subset_upperCone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:54:35.451298+00:00
-- url     : https://prove2.me/theorems/ca089d92-f20b-4e08-8345-7e092fdd8233
-- title:
--   Dilworth Theorem: antichain subset upper Cone
-- statement:
--   The Dilworth Theorem construction uses the antichain subset upper Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L147-L148
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L147-L148

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

theorem DilworthTheorem.antichain_subset_upperCone {S A : Finset α} (hAS : A ⊆ S) : A ⊆ upperCone S A := by sorry
