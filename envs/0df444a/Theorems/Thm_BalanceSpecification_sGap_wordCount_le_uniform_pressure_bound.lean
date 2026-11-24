-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_wordCount_le_uniform_pressure_bound
-- name    : BalanceSpecification.sGap_wordCount_le_uniform_pressure_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:09.513025+00:00
-- url     : https://prove2.me/theorems/a90a03a6-9cfc-4331-9700-8ff4d584f7f2
-- title:
--   Balance Specification: s Gap word Count le uniform pressure bound
-- statement:
--   The renewal pressure gives a uniform exponential envelope, without a
--   polynomial loss in the word length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L129-L196
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapBSM.lean#L129-L196

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

theorem BalanceSpecification.sGap_wordCount_le_uniform_pressure_bound
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty)
    {β : ℝ} (hβ : 1 < β)
    (hpressure : ∀ F : Finset ℕ, (∀ s ∈ F, s ∈ S) → ∑ s ∈ F, (β⁻¹)^(s + 1) ≤ 1)
    (n : ℕ) :
    (wordCount (language (sGapShift S)) n : ℝ) ≤
      (1 + β⁻¹ * ((1 - β⁻¹)⁻¹)^2) * β^n := by sorry
