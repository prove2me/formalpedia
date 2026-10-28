-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared7.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:27.911387+00:00
-- url     : https://prove2.me/theorems/8bb18c5c-a39d-4c78-b1ee-52afa8c50dc3
-- title:
--   Pair Graph Prepared7 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared7.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure7Coverage.lean, lines 9-29, SHA-256 c67858a27e34dde0368dc45f53f26f28bb16bcf9a2e0c9ccd449e48626dfbe47. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData7_Definitions_003

section
namespace D1Bound5.PairGraphPrepared7
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared7.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_7 * smallPairB_7 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_7) = true := by sorry

end D1Bound5.PairGraphPrepared7
end
