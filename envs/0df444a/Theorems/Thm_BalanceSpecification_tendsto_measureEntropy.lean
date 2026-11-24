-- Prove2me | Theorems.Thm_BalanceSpecification_tendsto_measureEntropy
-- name    : BalanceSpecification.tendsto_measureEntropy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:09:26.558932+00:00
-- url     : https://prove2.me/theorems/848a21f6-1b16-47dc-ac53-80ca4e87a60f
-- title:
--   Balance Specification: tendsto measure Entropy
-- statement:
--   The normalized block entropies converge to the source measure entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L256-L258
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L256-L258

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.tendsto_measureEntropy {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ) :
    Tendsto (fun n : ℕ => blockEntropy μ n / n) atTop (𝓝 (measureEntropy μ hInv)) := by sorry
