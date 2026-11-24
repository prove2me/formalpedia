-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_partial_pressure_le_one_of_entropy_lt
-- name    : BalanceSpecification.sGap_partial_pressure_le_one_of_entropy_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:34.853211+00:00
-- url     : https://prove2.me/theorems/41744716-17a8-4e81-bf86-3442e893d025
-- title:
--   Balance Specification: s Gap partial pressure le one of entropy lt
-- statement:
--   Weighted finite gap families cannot have pressure larger than one at a
--   base strictly above the shift's actual entropy exponential.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L129-L155
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L129-L155

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology

theorem BalanceSpecification.sGap_partial_pressure_le_one_of_entropy_lt
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : entropy (sGapShift S) (sGapShift_nonempty hS) < Real.log γ)
    (F : Finset ℕ) (hF : ∀ s ∈ F, s ∈ S) :
    ∑ s ∈ F, (γ⁻¹)^(s + 1) ≤ 1 := by sorry
