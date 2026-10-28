-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared48_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared48.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:35:57.48223+00:00
-- url     : https://prove2.me/theorems/e64f08fa-8568-4557-8c8a-fb0504236948
-- title:
--   Pair Graph Prepared48 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared48.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure48Coverage.lean, lines 9-29, SHA-256 cf547bf730123feb39f681d5a24fa79be0441f9efa99e2fe1672ec6e23f4d1e6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData48_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData48_Definitions_003

section
namespace D1Bound5.PairGraphPrepared48
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared48.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_48 * smallPairB_48 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_48) = true := by sorry

end D1Bound5.PairGraphPrepared48
end
