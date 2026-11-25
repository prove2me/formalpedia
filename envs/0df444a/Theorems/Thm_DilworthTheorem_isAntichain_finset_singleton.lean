-- Prove2me | Theorems.Thm_DilworthTheorem_isAntichain_finset_singleton
-- name    : DilworthTheorem.isAntichain_finset_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:49:15.955999+00:00
-- url     : https://prove2.me/theorems/001c7adc-85fe-54b0-923a-9f33691f8242
-- title:
--   Dilworth Theorem: is Antichain finset singleton
-- statement:
--   The Dilworth Theorem construction uses the is Antichain finset singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L56-L57
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L56-L57

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

theorem DilworthTheorem.isAntichain_finset_singleton (x : α) : IsAntichain (({x} : Finset α) : Set α) := by sorry
