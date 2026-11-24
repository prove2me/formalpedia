-- Prove2me | Theorems.Thm_BalanceSpecification_reverseLanguage_sGapShift
-- name    : BalanceSpecification.reverseLanguage_sGapShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:31.251331+00:00
-- url     : https://prove2.me/theorems/de11824a-fecb-4245-97ee-af4c53626d4a
-- title:
--   Balance Specification: reverse Language s Gap Shift
-- statement:
--   The Balance Specification construction uses the reverse Language s Gap Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L412-L419
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L412-L419

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

theorem BalanceSpecification.reverseLanguage_sGapShift [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) :
    reverseLanguage (language (sGapShift S)) = language (sGapShift S) := by sorry
