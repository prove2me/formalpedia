-- Prove2me | Theorems.Thm_DilworthTheorem_posetHeight_ge_one
-- name    : DilworthTheorem.posetHeight_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:59:53.053279+00:00
-- url     : https://prove2.me/theorems/dcf2fc97-d2b1-4122-8733-a4c5ae1ba2c2
-- title:
--   Dilworth Theorem: poset Height ge one
-- statement:
--   The Dilworth Theorem construction uses the poset Height ge one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L407-L410
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L407-L410

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

theorem DilworthTheorem.posetHeight_ge_one {S : Finset α} {x : α} (hx : x ∈ S) :
    1 ≤ posetHeight S x := by sorry
