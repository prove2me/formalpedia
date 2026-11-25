-- Prove2me | Theorems.Thm_DilworthTheorem_singleton_mem_chainsEndingAt
-- name    : DilworthTheorem.singleton_mem_chainsEndingAt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:30:42.890674+00:00
-- url     : https://prove2.me/theorems/3314d86f-8a17-5ec6-81ff-c4384a5e4c0f
-- title:
--   Dilworth Theorem: singleton mem chains Ending At
-- statement:
--   The Dilworth Theorem construction uses the singleton mem chains Ending At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L394-L397
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L394-L397

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

theorem DilworthTheorem.singleton_mem_chainsEndingAt {S : Finset α} {x : α} (hx : x ∈ S) :
    {x} ∈ chainsEndingAt S x := by sorry
