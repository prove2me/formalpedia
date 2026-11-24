-- Prove2me | Theorems.Thm_BalanceSpecification_finite_gapSet_of_finite_sGapShift
-- name    : BalanceSpecification.finite_gapSet_of_finite_sGapShift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:24.156827+00:00
-- url     : https://prove2.me/theorems/26507987-52c3-422a-abf1-2e93a1212a2e
-- title:
--   Balance Specification: finite gap Set of finite s Gap Shift
-- statement:
--   The Balance Specification construction uses the finite gap Set of finite s Gap Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L301-L306
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L301-L306

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

theorem BalanceSpecification.finite_gapSet_of_finite_sGapShift [TopologicalSpace Bool] {S : Set ℕ}
    (hX : (sGapShift S).carrier.Finite) : S.Finite := by sorry
