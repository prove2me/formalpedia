-- Prove2me | Theorems.Thm_BalanceSpecification_measureEntropy_eq_sInf
-- name    : BalanceSpecification.measureEntropy_eq_sInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:09:42.324808+00:00
-- url     : https://prove2.me/theorems/6d997f14-8699-4832-9357-1dcfdafdc609
-- title:
--   Balance Specification: measure Entropy eq s Inf
-- statement:
--   The source's complete infimum characterization over positive block lengths.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L261-L264
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L261-L264

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

theorem BalanceSpecification.measureEntropy_eq_sInf {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ) :
    measureEntropy μ hInv =
      sInf ((fun n : ℕ => blockEntropy μ n / n) '' Set.Ici 1) := by sorry
