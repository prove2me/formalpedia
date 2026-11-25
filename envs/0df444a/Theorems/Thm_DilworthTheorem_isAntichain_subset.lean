-- Prove2me | Theorems.Thm_DilworthTheorem_isAntichain_subset
-- name    : DilworthTheorem.isAntichain_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:33:10.695137+00:00
-- url     : https://prove2.me/theorems/62b66d0a-58a2-5fc7-82cb-9cecd8ed289c
-- title:
--   Dilworth Theorem: is Antichain subset
-- statement:
--   The Dilworth Theorem construction uses the is Antichain subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L59-L60
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L59-L60

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

theorem DilworthTheorem.isAntichain_subset {s t : Set α} (hst : s ⊆ t) (ht : IsAntichain t) : IsAntichain s := by sorry
