-- Prove2me | Theorems.Thm_DilworthTheorem_isChain_subset
-- name    : DilworthTheorem.isChain_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:30:39.263678+00:00
-- url     : https://prove2.me/theorems/c590b8c0-0695-5cba-87f3-6bdcd3acc2f9
-- title:
--   Dilworth Theorem: is Chain subset
-- statement:
--   The Dilworth Theorem construction uses the is Chain subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L48-L49
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L48-L49

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

theorem DilworthTheorem.isChain_subset {s t : Set α} (hst : s ⊆ t) (ht : IsChain t) : IsChain s := by sorry
