-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared21_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared21.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:13:39.326964+00:00
-- url     : https://prove2.me/theorems/cea807f8-279a-4267-997f-c968604a44f1
-- title:
--   Pair Graph Prepared21 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared21.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure21Coverage.lean, lines 9-29, SHA-256 790f2a265f18a38d647a4f0da1ae6868a8f54dea4bd5407d17369e485ca6cedf. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData21_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData21_Definitions_003

section
namespace D1Bound5.PairGraphPrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared21.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_21 * smallPairB_21 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_21) = true := by sorry

end D1Bound5.PairGraphPrepared21
end
