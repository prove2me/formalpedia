-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared12.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:47.439283+00:00
-- url     : https://prove2.me/theorems/5e27f2dd-ce5a-4cde-9e72-6ad4c3d1e8a6
-- title:
--   Pair Graph Prepared12 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared12.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure12Coverage.lean, lines 9-29, SHA-256 0b58c40a6eca773db716549bed5dac966d3e596e51c4286a6b9b706029e88612. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData12_Definitions

section
namespace D1Bound5.PairGraphPrepared12
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared12.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_12 * smallPairB_12 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_12) = true := by sorry

end D1Bound5.PairGraphPrepared12
end
