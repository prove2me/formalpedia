-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_getElem_infix_witness
-- name    : BalanceSpecification.FiveSymbol.getElem_infix_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:41.326863+00:00
-- url     : https://prove2.me/theorems/da2029cd-3bde-48d6-b9d9-ba0b777a12c6
-- title:
--   Five Symbol: get Elem infix witness
-- statement:
--   Read a letter at its offset in an explicitly located contiguous occurrence.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L211-L225
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L211-L225

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol

theorem BalanceSpecification.FiveSymbol.getElem_infix_witness {f W p q : Word Alphabet}
    (heq : W = p ++ f ++ q) {i : ℕ} (hi : i < f.length) :
    W[p.length + i]'(by
      have H := congrArg List.length heq
      simp only [List.length_append] at H
      omega) = f[i] := by sorry
