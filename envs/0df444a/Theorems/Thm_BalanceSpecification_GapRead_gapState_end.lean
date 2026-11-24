-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_gapState_end
-- name    : BalanceSpecification.GapRead.gapState_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:44.149449+00:00
-- url     : https://prove2.me/theorems/3be7e8b9-3c1d-4c14-a847-19dc6af88a25
-- title:
--   Gap Read: gap State end
-- statement:
--   The Gap Read construction uses the gap State end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L89-L95
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L89-L95

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

theorem BalanceSpecification.GapRead.gapState_end (h : GapRead S a u b) (ha : GapState S a) : GapState S b := by sorry
