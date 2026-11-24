-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_hasVariableSpecification_of_bounded_gaps
-- name    : BalanceSpecification.sGap_hasVariableSpecification_of_bounded_gaps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:47:18.26081+00:00
-- url     : https://prove2.me/theorems/d83ec205-16c4-4f28-8b96-5d471ef9f73c
-- title:
--   Balance Specification: s Gap has Variable Specification of bounded gaps
-- statement:
--   Bounded successive gaps give variable specification for the literal
--   S-gap coded shift, including finite `S` and the gap `0`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L242-L266
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L242-L266

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

theorem BalanceSpecification.sGap_hasVariableSpecification_of_bounded_gaps
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) (hg : HasBoundedSuccessiveGaps S) :
    HasVariableSpecification (sGapShift S) := by sorry
