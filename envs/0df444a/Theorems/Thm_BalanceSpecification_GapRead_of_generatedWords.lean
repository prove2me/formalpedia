-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_of_generatedWords
-- name    : BalanceSpecification.GapRead.of_generatedWords
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:47:15.421504+00:00
-- url     : https://prove2.me/theorems/0cfe9a49-900d-4455-b72e-fed99fcc8715
-- title:
--   Gap Read: of generated Words
-- statement:
--   The Gap Read construction uses the of generated Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L101-L108
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L101-L108

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

theorem BalanceSpecification.GapRead.of_generatedWords {w : Word Bool} (hw : w ∈ generatedWords (sGapCode S)) :
    GapRead S 0 w 0 := by sorry
