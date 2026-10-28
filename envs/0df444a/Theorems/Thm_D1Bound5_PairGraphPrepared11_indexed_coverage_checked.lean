-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared11_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared11.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:16.157039+00:00
-- url     : https://prove2.me/theorems/186ab6e8-7555-493d-ab2b-2451e6ac6cbb
-- title:
--   Pair Graph Prepared11 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared11.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure11Coverage.lean, lines 9-29, SHA-256 7bc47e349845f51fdca070a1ae349e8e36f2d260b39a84fea6ee96127ffc5170. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs11_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData11_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData11_Definitions_003

section
namespace D1Bound5.PairGraphPrepared11
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared11.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_11 * smallPairB_11 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_11) = true := by sorry

end D1Bound5.PairGraphPrepared11
end
