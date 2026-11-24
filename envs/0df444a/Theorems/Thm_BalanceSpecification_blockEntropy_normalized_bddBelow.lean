-- Prove2me | Theorems.Thm_BalanceSpecification_blockEntropy_normalized_bddBelow
-- name    : BalanceSpecification.blockEntropy_normalized_bddBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:09:33.179293+00:00
-- url     : https://prove2.me/theorems/ed8fd01f-1706-4594-838e-86e870fe22a8
-- title:
--   Balance Specification: block Entropy normalized bdd Below
-- statement:
--   The Balance Specification construction uses the block Entropy normalized bdd Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L244-L248
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean#L244-L248

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
omit [DiscreteTopology A] [BorelSpace A]

theorem BalanceSpecification.blockEntropy_normalized_bddBelow (μ : ProbabilityMeasure X.carrier) :
    BddBelow (Set.range fun n : ℕ => blockEntropy μ n / n) := by sorry
