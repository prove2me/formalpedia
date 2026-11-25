-- Prove2me | Theorems.Thm_DilworthTheorem_posetHeight_le
-- name    : DilworthTheorem.posetHeight_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:01:08.03101+00:00
-- url     : https://prove2.me/theorems/0dfad2f5-0bd7-48c7-b170-310f99f9ef51
-- title:
--   Dilworth Theorem: poset Height le
-- statement:
--   The Dilworth Theorem construction uses the poset Height le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L412-L415
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L412-L415

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

theorem DilworthTheorem.posetHeight_le {S : Finset α} {x : α} {m : ℕ}
    (h_chain : ∀ C ⊆ S, IsChain (C : Set α) → C.card ≤ m) :
    posetHeight S x ≤ m := by sorry
