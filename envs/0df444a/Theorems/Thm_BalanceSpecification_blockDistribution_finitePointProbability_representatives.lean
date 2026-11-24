-- Prove2me | Theorems.Thm_BalanceSpecification_blockDistribution_finitePointProbability_representatives
-- name    : BalanceSpecification.blockDistribution_finitePointProbability_representatives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:13:05.195647+00:00
-- url     : https://prove2.me/theorems/2fc0aaad-3253-4836-9c53-27dc160629f1
-- title:
--   Balance Specification: block Distribution finite Point Probability representatives
-- statement:
--   Choosing one configuration for each admissible word yields a genuinely
--   uniform distribution on the length-`N` cylinder partition.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L130-L148
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L130-L148

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

theorem BalanceSpecification.blockDistribution_finitePointProbability_representatives (N : ℕ)
    [Nonempty ↥(wordFinset (language X) N)]
    (x : ↥(wordFinset (language X) N) → X.carrier)
    (hx : ∀ w, block (x w).val 0 N = w.val)
    (w : ↥(wordFinset (language X) N)) :
    blockDistribution (finitePointProbability x) N w = 1 / wordCount (language X) N := by sorry
