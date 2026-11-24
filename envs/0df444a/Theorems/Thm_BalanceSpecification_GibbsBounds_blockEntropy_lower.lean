-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_blockEntropy_lower
-- name    : BalanceSpecification.GibbsBounds.blockEntropy_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:31.344552+00:00
-- url     : https://prove2.me/theorems/5eba68db-c910-4523-8c20-a5ff280e55c0
-- title:
--   Gibbs Bounds: block Entropy lower
-- statement:
--   The upper Gibbs bound supplies the lower block-entropy estimate.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean#L31-L54
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean#L31-L54

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

theorem BalanceSpecification.GibbsBounds.blockEntropy_lower {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K) (n : ℕ) :
    (n : ℝ) * entropy X hX - Real.log K ≤ blockEntropy μ n := by sorry
