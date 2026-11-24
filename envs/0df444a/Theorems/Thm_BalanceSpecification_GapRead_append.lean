-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_append
-- name    : BalanceSpecification.GapRead.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:32.009845+00:00
-- url     : https://prove2.me/theorems/7246ed55-7659-47ec-b10b-2daa2d5bae0e
-- title:
--   Gap Read: append
-- statement:
--   The Gap Read construction uses the append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L41-L46
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L41-L46

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

theorem BalanceSpecification.GapRead.append (hu : GapRead S a u b) (hv : GapRead S b v c) :
    GapRead S a (u ++ v) c := by sorry
