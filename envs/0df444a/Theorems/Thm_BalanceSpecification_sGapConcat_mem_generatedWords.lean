-- Prove2me | Theorems.Thm_BalanceSpecification_sGapConcat_mem_generatedWords
-- name    : BalanceSpecification.sGapConcat_mem_generatedWords
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:02.185088+00:00
-- url     : https://prove2.me/theorems/c9fb4221-8859-4b24-8dec-149eee2c856f
-- title:
--   Balance Specification: s Gap Concat mem generated Words
-- statement:
--   The Balance Specification construction uses the s Gap Concat mem generated Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L108-L113
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean#L108-L113

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

theorem BalanceSpecification.sGapConcat_mem_generatedWords {S : Set ℕ} {r : ℕ} {f : Fin r → ℕ}
    (hf : ∀ i, f i ∈ S) : sGapConcat f ∈ generatedWords (sGapCode S) := by sorry
