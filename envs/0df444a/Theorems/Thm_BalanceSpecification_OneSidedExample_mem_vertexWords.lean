-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_mem_vertexWords
-- name    : BalanceSpecification.OneSidedExample.mem_vertexWords
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:44:21.558984+00:00
-- url     : https://prove2.me/theorems/2c4ca2dc-0265-4219-aec4-869fd32bc5fd
-- title:
--   One Sided Example: mem vertex Words
-- statement:
--   The One Sided Example construction uses the mem vertex Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L42-L51
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean#L42-L51

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.mem_vertexWords {s : Vertex} {n : ℕ} {w : Word Alphabet} :
    w ∈ vertexWords s n ↔ w.length = n ∧ ∃ t, Walk s w t := by sorry
