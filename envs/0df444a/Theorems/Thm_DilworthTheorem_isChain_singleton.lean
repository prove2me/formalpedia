-- Prove2me | Theorems.Thm_DilworthTheorem_isChain_singleton
-- name    : DilworthTheorem.isChain_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:45:40.315151+00:00
-- url     : https://prove2.me/theorems/ec87c237-11cf-4b37-8675-fa96d52c3f04
-- title:
--   Dilworth Theorem: is Chain singleton
-- statement:
--   The Dilworth Theorem construction uses the is Chain singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L42-L43
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L42-L43

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

theorem DilworthTheorem.isChain_singleton (x : α) : IsChain ({x} : Set α) := by sorry
