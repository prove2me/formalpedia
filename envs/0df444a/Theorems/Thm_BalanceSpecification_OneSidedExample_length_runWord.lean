-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
-- name    : BalanceSpecification.OneSidedExample.length_runWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:29.013534+00:00
-- url     : https://prove2.me/theorems/86c2fc1a-9f58-4758-9650-91899b49eea7
-- title:
--   One Sided Example: length run Word
-- statement:
--   The One Sided Example construction uses the length run Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraph.lean#L92-L96
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraph.lean#L92-L96

module
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.length_runWord (s : Vertex) (ds : List Bool) :
    (runWord s ds).length = ds.length := by sorry
