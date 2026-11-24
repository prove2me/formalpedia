-- Prove2me | Theorems.Thm_BalanceSpecification_measureEntropy_eq_iInf
-- name    : BalanceSpecification.measureEntropy_eq_iInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:48.825494+00:00
-- url     : https://prove2.me/theorems/f134f6b1-a51b-491b-ac61-a4d04451e70f
-- title:
--   Balance Specification: measure Entropy eq i Inf
-- statement:
--   The measure-entropy infimum can equivalently be indexed by positive natural lengths.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L90-L101
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L90-L101

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.measureEntropy_eq_iInf {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ) :
    measureEntropy μ hInv = ⨅ n : {n : ℕ // 1 ≤ n}, blockEntropy μ n.val / n.val := by sorry
