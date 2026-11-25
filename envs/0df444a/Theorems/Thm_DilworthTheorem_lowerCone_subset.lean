-- Prove2me | Theorems.Thm_DilworthTheorem_lowerCone_subset
-- name    : DilworthTheorem.lowerCone_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:30:39.216451+00:00
-- url     : https://prove2.me/theorems/9e1c6d95-d2e7-5e6c-b9f1-9f71e6e040d7
-- title:
--   Dilworth Theorem: lower Cone subset
-- statement:
--   The Dilworth Theorem construction uses the lower Cone subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L140-L140
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L140-L140

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

theorem DilworthTheorem.lowerCone_subset (S A : Finset α) : lowerCone S A ⊆ S := by sorry
