-- Prove2me | Theorems.Thm_BalanceSpecification_sGapListConcat_mem_generatedWords
-- name    : BalanceSpecification.sGapListConcat_mem_generatedWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:56.781226+00:00
-- url     : https://prove2.me/theorems/84696dd8-ccf7-498e-a734-7671af254d4c
-- title:
--   Balance Specification: s Gap List Concat mem generated Words
-- statement:
--   The Balance Specification construction uses the s Gap List Concat mem generated Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L101-L106
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L101-L106

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification

theorem BalanceSpecification.sGapListConcat_mem_generatedWords {S : Set ℕ} {ss : List ℕ}
    (hs : ∀ s ∈ ss, s ∈ S) : sGapListConcat ss ∈ generatedWords (sGapCode S) := by sorry
