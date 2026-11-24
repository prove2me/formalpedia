-- Prove2me | Theorems.Thm_BalanceSpecification_blockEntropy_finitePointProbability_representatives
-- name    : BalanceSpecification.blockEntropy_finitePointProbability_representatives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:56.817703+00:00
-- url     : https://prove2.me/theorems/a43abea4-fbed-4997-8b97-f27d4fa128cc
-- title:
--   Balance Specification: block Entropy finite Point Probability representatives
-- statement:
--   The initial long-word measure has exactly the logarithmic word-count entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L151-L163
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L151-L163

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

theorem BalanceSpecification.blockEntropy_finitePointProbability_representatives (N : ℕ)
    [Nonempty ↥(wordFinset (language X) N)]
    (x : ↥(wordFinset (language X) N) → X.carrier)
    (hx : ∀ w, block (x w).val 0 N = w.val) :
    blockEntropy (finitePointProbability x) N = Real.log (wordCount (language X) N) := by sorry
