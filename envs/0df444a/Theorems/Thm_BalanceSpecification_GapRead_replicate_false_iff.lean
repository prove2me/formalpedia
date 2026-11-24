-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_replicate_false_iff
-- name    : BalanceSpecification.GapRead.replicate_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:22.220388+00:00
-- url     : https://prove2.me/theorems/976c19e4-468e-4b52-aca0-91fa3158d94d
-- title:
--   Gap Read: replicate false iff
-- statement:
--   The Gap Read construction uses the replicate false iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L68-L87
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L68-L87

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

theorem BalanceSpecification.GapRead.replicate_false_iff {n : ℕ} :
    GapRead S a (List.replicate n false) b ↔ a = b + n := by sorry
