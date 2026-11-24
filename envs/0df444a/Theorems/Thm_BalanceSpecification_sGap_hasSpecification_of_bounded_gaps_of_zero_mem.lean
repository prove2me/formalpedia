-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_hasSpecification_of_bounded_gaps_of_zero_mem
-- name    : BalanceSpecification.sGap_hasSpecification_of_bounded_gaps_of_zero_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:43.014119+00:00
-- url     : https://prove2.me/theorems/3f4501ec-660e-43ea-bd80-513a4b77e92b
-- title:
--   Balance Specification: s Gap has Specification of bounded gaps of zero mem
-- statement:
--   When `0 ∈ S`, the bounded bridges can be padded by arbitrary strings of
--   `1`s at the renewal state, giving one fixed specification gap.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L458-L487
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L458-L487

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

theorem BalanceSpecification.sGap_hasSpecification_of_bounded_gaps_of_zero_mem
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (h0 : 0 ∈ S) (hg : HasBoundedSuccessiveGaps S) :
    HasSpecification (sGapShift S) := by sorry
