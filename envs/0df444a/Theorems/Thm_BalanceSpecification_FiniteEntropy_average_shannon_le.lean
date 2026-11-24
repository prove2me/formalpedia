-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_average_shannon_le
-- name    : BalanceSpecification.FiniteEntropy.average_shannon_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:59.782595+00:00
-- url     : https://prove2.me/theorems/208b99a1-b12c-445b-97d0-e19c9650009a
-- title:
--   Finite Entropy: average shannon le
-- statement:
--   Equal finite averaging is the case used for orbit averages of word measures.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L58-L67
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L58-L67

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

theorem BalanceSpecification.FiniteEntropy.average_shannon_le [Nonempty κ] {p : κ → ι → ℝ}
    (hp : ∀ k i, 0 ≤ p k i) :
    (Fintype.card κ : ℝ)⁻¹ * ∑ k, shannon (p k) ≤
      shannon (fun i => (Fintype.card κ : ℝ)⁻¹ * ∑ k, p k i) := by sorry
