-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_loop_mem_generatedWords
-- name    : BalanceSpecification.OneSidedExample.Walk.loop_mem_generatedWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:54.559408+00:00
-- url     : https://prove2.me/theorems/3a402def-4a1a-4941-84f8-d95872a353bf
-- title:
--   Walk: loop mem generated Words
-- statement:
--   The Walk construction uses the loop mem generated Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L87-L88
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L87-L88

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.Walk.loop_mem_generatedWords {w : Word Alphabet} (h : Walk (.p 0) w (.p 0)) :
    w ∈ generatedWords code := by sorry
