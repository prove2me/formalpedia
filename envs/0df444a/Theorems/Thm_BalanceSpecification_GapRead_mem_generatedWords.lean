-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_mem_generatedWords
-- name    : BalanceSpecification.GapRead.mem_generatedWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:54.156281+00:00
-- url     : https://prove2.me/theorems/923fa89a-58af-44bd-8284-ea8203b7fbec
-- title:
--   Gap Read: mem generated Words
-- statement:
--   The Gap Read construction uses the mem generated Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L120-L133
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L120-L133

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

theorem BalanceSpecification.GapRead.mem_generatedWords {w : Word Bool} (h : GapRead S 0 w 0) :
    w ∈ generatedWords (sGapCode S) := by sorry
