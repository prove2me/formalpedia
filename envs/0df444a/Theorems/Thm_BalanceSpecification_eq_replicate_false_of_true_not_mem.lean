-- Prove2me | Theorems.Thm_BalanceSpecification_eq_replicate_false_of_true_not_mem
-- name    : BalanceSpecification.eq_replicate_false_of_true_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:08.031538+00:00
-- url     : https://prove2.me/theorems/d02d122e-a46e-47d7-b83d-c2ccd4ba3205
-- title:
--   Balance Specification: eq replicate false of true not mem
-- statement:
--   The Balance Specification construction uses the eq replicate false of true not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L172-L181
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L172-L181

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

theorem BalanceSpecification.eq_replicate_false_of_true_not_mem {w : Word Bool} (h : true ∉ w) :
    w = List.replicate w.length false := by sorry
