-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared43_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared43.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:33:44.081984+00:00
-- url     : https://prove2.me/theorems/c8506a41-68b5-484a-9a42-530c63199c61
-- title:
--   Pair Graph Prepared43 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared43.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure43Coverage.lean, lines 9-29, SHA-256 81b93ba58505765b7bd849efe3f6c5b1727888a0809f05c00f105a23e512e992. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData43_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData43_Definitions_003

section
namespace D1Bound5.PairGraphPrepared43
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared43.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_43 * smallPairB_43 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_43) = true := by sorry

end D1Bound5.PairGraphPrepared43
end
