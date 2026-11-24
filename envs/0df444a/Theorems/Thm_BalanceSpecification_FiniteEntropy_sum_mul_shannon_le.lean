-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_sum_mul_shannon_le
-- name    : BalanceSpecification.FiniteEntropy.sum_mul_shannon_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:15.671669+00:00
-- url     : https://prove2.me/theorems/b8d2f072-89c0-4733-85f0-c503358fbeda
-- title:
--   Finite Entropy: sum mul shannon le
-- statement:
--   Finite Shannon entropy is concave under arbitrary probability weights.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L41-L55
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L41-L55

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
open BalanceSpecification.FiniteEntropy
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem BalanceSpecification.FiniteEntropy.sum_mul_shannon_le {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1)
    {p : κ → ι → ℝ} (hp : ∀ k i, 0 ≤ p k i) :
    ∑ k, w k * shannon (p k) ≤ shannon (fun i => ∑ k, w k * p k i) := by sorry
