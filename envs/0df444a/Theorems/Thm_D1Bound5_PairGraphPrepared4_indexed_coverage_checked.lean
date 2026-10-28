-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared4_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared4.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:06:47.756686+00:00
-- url     : https://prove2.me/theorems/21cfc3b4-e06a-462e-85ff-b9120aa723c8
-- title:
--   Pair Graph Prepared4 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared4.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure4Coverage.lean, lines 9-29, SHA-256 3bd34284f35ec6756bebfd959652746a15922c9fbe7c9799af61443361efda63. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData4_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData4_Definitions_003

section
namespace D1Bound5.PairGraphPrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared4.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_4 * smallPairB_4 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_4) = true := by sorry

end D1Bound5.PairGraphPrepared4
end
