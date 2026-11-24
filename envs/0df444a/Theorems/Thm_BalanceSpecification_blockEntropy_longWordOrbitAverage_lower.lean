-- Prove2me | Theorems.Thm_BalanceSpecification_blockEntropy_longWordOrbitAverage_lower
-- name    : BalanceSpecification.blockEntropy_longWordOrbitAverage_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:13:00.857284+00:00
-- url     : https://prove2.me/theorems/9eaae989-2422-415a-8c4a-45bef9783405
-- title:
--   Balance Specification: block Entropy long Word Orbit Average lower
-- statement:
--   The finite blocking estimate gives the entropy lower bound for the actual
--   orbit average of a uniform long-word measure.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L174-L207
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L174-L207

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

theorem BalanceSpecification.blockEntropy_longWordOrbitAverage_lower (hX : X.carrier.Nonempty)
    (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N + 1)
    [Nonempty ↥(wordFinset (language X) (N + 1))]
    (x : ↥(wordFinset (language X) (N + 1)) → X.carrier)
    (hx : ∀ w, block (x w).val 0 (N + 1) = w.val) :
    (n : ℝ) * (Real.log (wordCount (language X) (N + 1)) / ((N + 1 : ℕ) : ℝ)) -
        (3 * (n : ℝ)^2 * Real.log (Fintype.card A)) / ((N + 1 : ℕ) : ℝ) ≤
      blockEntropy (finiteOrbitProbability (shiftMap X) x N) n := by sorry
