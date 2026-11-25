-- Prove2me | Theorems.Thm_DilworthTheorem_exists_maximal_chain
-- name    : DilworthTheorem.exists_maximal_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:50:25.616106+00:00
-- url     : https://prove2.me/theorems/437f02d2-b09c-418e-8f54-111a2ea4848f
-- title:
--   Dilworth Theorem: exists maximal chain
-- statement:
--   The Dilworth Theorem construction uses the exists maximal chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L94-L132
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/DilworthTheorem.lean#L94-L132

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

theorem DilworthTheorem.exists_maximal_chain (S : Finset α) (hS : S.Nonempty) :
    ∃ C : Finset α, C ⊆ S ∧ C.Nonempty ∧ IsChain (C : Set α) ∧
      (∃ cmax ∈ C, ∀ x ∈ S, cmax ≤ x → x = cmax) ∧
      (∃ cmin ∈ C, ∀ x ∈ S, x ≤ cmin → x = cmin) := by sorry
