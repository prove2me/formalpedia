-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared40_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared40.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:32.657458+00:00
-- url     : https://prove2.me/theorems/9a765b71-0019-4f2a-be18-6be757f3907e
-- title:
--   Pair Graph Prepared40 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared40.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure40Coverage.lean, lines 9-12, SHA-256 86cd66c6f974a553afbc7f7b6e3ff383f55ba90d35217de8488fe142bce175e5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData40_Definitions_003

section
namespace D1Bound5.PairGraphPrepared40
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared40.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_40 * smallPairB_40 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_40) = true := by sorry

end D1Bound5.PairGraphPrepared40
end
