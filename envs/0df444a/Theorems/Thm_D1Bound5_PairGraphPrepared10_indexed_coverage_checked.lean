-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared10_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared10.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:02:45.041595+00:00
-- url     : https://prove2.me/theorems/cc1d03ee-ec0d-4601-b151-ef20758308fe
-- title:
--   Pair Graph Prepared10 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared10.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure10Coverage.lean, lines 9-29, SHA-256 4f5ad4794fb9099a90d5a26c113d58b08a47df5c4982a34db1b60dfd4dd7356b. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData10_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData10_Definitions_003

section
namespace D1Bound5.PairGraphPrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared10.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_10 * smallPairB_10 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_10) = true := by sorry

end D1Bound5.PairGraphPrepared10
end
