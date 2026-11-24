-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_bounded_gaps_of_rightBalanced
-- name    : BalanceSpecification.sGap_bounded_gaps_of_rightBalanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:20.533804+00:00
-- url     : https://prove2.me/theorems/0af2e066-88f3-49cb-86f0-ba715e83b80b
-- title:
--   Balance Specification: s Gap bounded gaps of right Balanced
-- statement:
--   One-sided right-balancedness rules out unbounded consecutive gaps. The
--   argument uses actual bounded word complexity and infinitely many distinct
--   periodic code configurations, without assuming positive entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L335-L375
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L335-L375

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

theorem BalanceSpecification.sGap_bounded_gaps_of_rightBalanced [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) (hR : RightBalanced (language (sGapShift S))) :
    HasBoundedSuccessiveGaps S := by sorry
