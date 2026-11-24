-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_partial_pressure_le_one
-- name    : BalanceSpecification.sGap_partial_pressure_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:27.688282+00:00
-- url     : https://prove2.me/theorems/6fc444c8-83ec-4fee-a6f9-91b8fbf6f24a
-- title:
--   Balance Specification: s Gap partial pressure le one
-- statement:
--   Finite partial pressure bounds follow from the actual renewal pressure sum.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L112-L125
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L112-L125

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology

theorem BalanceSpecification.sGap_partial_pressure_le_one {S : Set ℕ} {β : ℝ} (hβ : 0 < β)
    (hroot : HasSum (fun s : S => (β⁻¹)^(s.val + 1)) 1)
    (F : Finset ℕ) (hF : ∀ s ∈ F, s ∈ S) :
    ∑ s ∈ F, (β⁻¹)^(s + 1) ≤ 1 := by sorry
