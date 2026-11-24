-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_runWord_injective
-- name    : BalanceSpecification.OneSidedExample.runWord_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:12:39.316649+00:00
-- url     : https://prove2.me/theorems/d91fdda6-2a2a-4f85-b454-f044a6907ba9
-- title:
--   One Sided Example: run Word injective
-- statement:
--   The One Sided Example construction uses the run Word injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraph.lean#L105-L121
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraph.lean#L105-L121

module
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.runWord_injective (s : Vertex) : Function.Injective (runWord s) := by sorry
