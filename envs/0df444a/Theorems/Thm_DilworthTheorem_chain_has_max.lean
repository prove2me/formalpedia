-- Prove2me | Theorems.Thm_DilworthTheorem_chain_has_max
-- name    : DilworthTheorem.chain_has_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:49:45.40465+00:00
-- url     : https://prove2.me/theorems/4b9d3837-6696-5cfb-99cb-0c5a15f9c4ec
-- title:
--   Dilworth Theorem: chain has max
-- statement:
--   The Dilworth Theorem construction uses the chain has max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L72-L81
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L72-L81

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

theorem DilworthTheorem.chain_has_max (C : Finset α) (hC_nonempty : C.Nonempty) (hC_chain : IsChain (C : Set α)) :
    ∃ m ∈ C, ∀ x ∈ C, x ≤ m := by sorry
