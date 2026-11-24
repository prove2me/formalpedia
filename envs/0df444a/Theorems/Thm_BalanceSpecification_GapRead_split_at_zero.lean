-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_split_at_zero
-- name    : BalanceSpecification.GapRead.split_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:57.914887+00:00
-- url     : https://prove2.me/theorems/1b5eb65d-81bd-4321-b317-61627497daae
-- title:
--   Gap Read: split at zero
-- statement:
--   The Gap Read construction uses the split at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L110-L118
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L110-L118

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open BalanceSpecification.GapRead
variable {S : Set ℕ} {a b c : ℕ} {u v : Word Bool}

theorem BalanceSpecification.GapRead.split_at_zero {w : Word Bool} (h : GapRead S a w 0) :
    ∃ v, w = List.replicate a false ++ v ∧ GapRead S 0 v 0 := by sorry
