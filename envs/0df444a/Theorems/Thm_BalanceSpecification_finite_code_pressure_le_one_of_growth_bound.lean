-- Prove2me | Theorems.Thm_BalanceSpecification_finite_code_pressure_le_one_of_growth_bound
-- name    : BalanceSpecification.finite_code_pressure_le_one_of_growth_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:31.116264+00:00
-- url     : https://prove2.me/theorems/8815e58a-82f2-48dc-a3f1-2ad87d8f7c91
-- title:
--   Balance Specification: finite code pressure le one of growth bound
-- statement:
--   A finite uniquely decodable family contained in a language has weighted
--   code mass at most one whenever its word counts satisfy the stated exponential envelope.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L24-L109
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapEntropy.lean#L24-L109

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

theorem BalanceSpecification.finite_code_pressure_le_one_of_growth_bound
    {A I : Type*} [Fintype A] [Fintype I] [TopologicalSpace A]
    {X : ShiftSpace A} (c : I → Word A) {γ C : ℝ}
    (hγ : 0 < γ) (_hC : 0 < C)
    (hcounts : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤ C * γ ^ n)
    (hinj : ∀ r : ℕ, Function.Injective
      (fun f : Fin r → I => (List.ofFn (fun i => c (f i))).flatten))
    (hmem : ∀ (r : ℕ) (f : Fin r → I),
      (List.ofFn (fun i => c (f i))).flatten ∈ language X) :
    ∑ i, (γ⁻¹) ^ (c i).length ≤ 1 := by sorry
