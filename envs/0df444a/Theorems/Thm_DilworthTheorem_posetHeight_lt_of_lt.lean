-- Prove2me | Theorems.Thm_DilworthTheorem_posetHeight_lt_of_lt
-- name    : DilworthTheorem.posetHeight_lt_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:01:14.118014+00:00
-- url     : https://prove2.me/theorems/5c83d767-6874-5c39-b16d-c3b246cd05c0
-- title:
--   Dilworth Theorem: poset Height lt of lt
-- statement:
--   The Dilworth Theorem construction uses the poset Height lt of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L417-L436
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L417-L436

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

theorem DilworthTheorem.posetHeight_lt_of_lt {S : Finset α} {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    posetHeight S x < posetHeight S y := by sorry
