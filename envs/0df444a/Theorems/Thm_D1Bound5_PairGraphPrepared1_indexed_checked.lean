-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared1_indexed_checked
-- name    : D1Bound5.PairGraphPrepared1.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:23:41.436991+00:00
-- url     : https://prove2.me/theorems/e7f26930-69cb-42d0-a140-05541d6df28b
-- title:
--   Pair Graph Prepared1 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared1.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure1.lean, lines 21-102, SHA-256 1c5b7889253b1e9e774a58da7481e5ff5d498dd85f6f4662f2afa0d5743bac34. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs1_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData1_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData1_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared1

theorem _root_.D1Bound5.PairGraphPrepared1.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_1 smallPairB_1 anchorRoot
      (10^1100) smallPairClosure_1 witnesses destinations = true := by sorry



end D1Bound5
end
