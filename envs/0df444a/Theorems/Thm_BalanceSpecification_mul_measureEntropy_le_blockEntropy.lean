-- Prove2me | Theorems.Thm_BalanceSpecification_mul_measureEntropy_le_blockEntropy
-- name    : BalanceSpecification.mul_measureEntropy_le_blockEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:15.033937+00:00
-- url     : https://prove2.me/theorems/7451ebf4-9e4b-45be-b745-e7a5ad05dd38
-- title:
--   Balance Specification: mul measure Entropy le block Entropy
-- statement:
--   Every block entropy dominates length times the limiting measure entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L278-L286
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L278-L286

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

theorem BalanceSpecification.mul_measureEntropy_le_blockEntropy {μ : ProbabilityMeasure X.carrier}
    (hInv : IsInvariant μ) (n : ℕ) :
    (n : ℝ) * measureEntropy μ hInv ≤ blockEntropy μ n := by sorry
