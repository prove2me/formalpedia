-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_wordCount_le_restricted_renewal_sum
-- name    : BalanceSpecification.sGap_wordCount_le_restricted_renewal_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:04.614703+00:00
-- url     : https://prove2.me/theorems/9aecb574-0ca1-4079-839f-3f8219069ab8
-- title:
--   Balance Specification: s Gap word Count le restricted renewal sum
-- statement:
--   The exact zero-prefix/renewal-word/last-marker decomposition needs only
--   nonnegative interior lengths; invalid boundary pairs contribute zero.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L78-L125
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L78-L125

module
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBSM
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology

theorem BalanceSpecification.sGap_wordCount_le_restricted_renewal_sum
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty) (n : ℕ) :
    wordCount (language (sGapShift S)) n ≤
      1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        if a + m + 1 ≤ n then renewalCount S (n - a - m - 1) else 0 := by sorry
