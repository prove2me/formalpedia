-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_generatedWords_loop
-- name    : BalanceSpecification.OneSidedExample.generatedWords_loop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:13:06.975117+00:00
-- url     : https://prove2.me/theorems/784a7c47-ec5b-457d-aa10-2fbea821c881
-- title:
--   One Sided Example: generated Words loop
-- statement:
--   Concatenations of generators label based loops.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L131-L139
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L131-L139

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.generatedWords_loop {w : Word Alphabet} (hw : w ∈ generatedWords code) :
    Walk (.p 0) w (.p 0) := by sorry
