-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_mem_language
-- name    : BalanceSpecification.OneSidedExample.Walk.mem_language
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:10.396878+00:00
-- url     : https://prove2.me/theorems/698a295f-c232-4228-887f-7a25ab35461b
-- title:
--   Walk: mem language
-- statement:
--   Every finite graph path occurs in the literal coded shift: close it to a
--   based loop and parse that loop into source generators.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L153-L158
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L153-L158

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.Walk.mem_language {s t : Vertex} {w : Word Alphabet} (h : Walk s w t) :
    w ∈ language shift := by sorry
