-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared19_indexed_checked
-- name    : D1Bound5.PairGraphPrepared19.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:00:47.709381+00:00
-- url     : https://prove2.me/theorems/6d20fbc4-f61e-418e-8a80-1c743ad4a567
-- title:
--   Pair Graph Prepared19 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared19.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure19.lean, lines 23-116, SHA-256 b30398822eeed7098ccbea3abf18123621d25d3edf023bff9cf8d592bd359619. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData19_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData19_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared19

theorem _root_.D1Bound5.PairGraphPrepared19.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_19 smallPairB_19 anchorRoot
      (10^1100) smallPairClosure_19 witnesses destinations = true := by sorry



end D1Bound5
end
