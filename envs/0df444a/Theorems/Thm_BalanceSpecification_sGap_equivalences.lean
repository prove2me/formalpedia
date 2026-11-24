-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_equivalences
-- name    : BalanceSpecification.sGap_equivalences
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:34:26.261823+00:00
-- url     : https://prove2.me/theorems/3aa04d2a-25a1-4509-8893-66d728755629
-- title:
--   Balance Specification: s Gap equivalences
-- statement:
--   The complete four-property equivalence in the S-gap proposition. The single
--   joint declaration includes finite sets, singletons, and the allowed gap `0`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L431-L447
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L431-L447

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

theorem BalanceSpecification.sGap_equivalences [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) :
    (HasBoundedSuccessiveGaps S ↔ HasVariableSpecification (sGapShift S)) ∧
    (HasBoundedSuccessiveGaps S ↔ BiBalanced (language (sGapShift S))) ∧
    (HasBoundedSuccessiveGaps S ↔
      RightBalanced (language (sGapShift S)) ∨ LeftBalanced (language (sGapShift S))) := by sorry
