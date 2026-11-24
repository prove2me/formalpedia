-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_split
-- name    : BalanceSpecification.OneSidedExample.Walk.split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:08.059957+00:00
-- url     : https://prove2.me/theorems/ed7f28aa-47ad-46a3-b4f0-3c9a1059348e
-- title:
--   Walk: split
-- statement:
--   The Walk construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraph.lean#L40-L48
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraph.lean#L40-L48

module
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.Walk.split {s z : Vertex} {u v : Word Alphabet}
    (h : Walk s (u ++ v) z) : ∃ t, Walk s u t ∧ Walk t v z := by sorry
