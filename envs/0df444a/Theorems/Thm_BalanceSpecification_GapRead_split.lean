-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_split
-- name    : BalanceSpecification.GapRead.split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:19.855806+00:00
-- url     : https://prove2.me/theorems/9af85ad8-e6a2-418f-906c-72f7d295d88a
-- title:
--   Gap Read: split
-- statement:
--   The Gap Read construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L48-L59
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L48-L59

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

theorem BalanceSpecification.GapRead.split (h : GapRead S a (u ++ v) c) :
    ∃ b, GapRead S a u b ∧ GapRead S b v c := by sorry
