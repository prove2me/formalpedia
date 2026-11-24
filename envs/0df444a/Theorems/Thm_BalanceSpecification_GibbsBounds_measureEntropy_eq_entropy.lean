-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_measureEntropy_eq_entropy
-- name    : BalanceSpecification.GibbsBounds.measureEntropy_eq_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:57.370945+00:00
-- url     : https://prove2.me/theorems/c5c1441c-9cfb-47df-876f-63453efe401a
-- title:
--   Gibbs Bounds: measure Entropy eq entropy
-- statement:
--   An invariant Gibbs measure attains the actual topological entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean#L57-L69
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean#L57-L69

module
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.GibbsBounds.measureEntropy_eq_entropy {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (hInv : IsInvariant μ) : measureEntropy μ hInv = entropy X hX := by sorry
