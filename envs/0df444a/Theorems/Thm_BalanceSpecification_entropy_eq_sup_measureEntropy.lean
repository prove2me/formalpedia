-- Prove2me | Theorems.Thm_BalanceSpecification_entropy_eq_sup_measureEntropy
-- name    : BalanceSpecification.entropy_eq_sup_measureEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:18:49.826017+00:00
-- url     : https://prove2.me/theorems/9058377b-e9aa-4295-a4ff-8e1a428cfbd4
-- title:
--   Balance Specification: entropy eq sup measure Entropy
-- statement:
--   The full variational principle: topological entropy is the supremum of
--   measure entropies of all invariant Borel probability measures.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L253-L268
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L253-L268

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.entropy_eq_sup_measureEntropy (hX : X.carrier.Nonempty) :
    entropy X hX = sSup {r : ℝ | ∃ (μ : ProbabilityMeasure X.carrier) (hInv : IsInvariant μ),
      measureEntropy μ hInv = r} := by sorry
