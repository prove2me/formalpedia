-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared11_indexed_checked
-- name    : D1Bound5.PairGraphPrepared11.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:10:33.09016+00:00
-- url     : https://prove2.me/theorems/53394ad2-5f6f-4a74-a821-1b78d464a6e9
-- title:
--   Pair Graph Prepared11 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared11.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure11.lean, lines 21-102, SHA-256 07e7bbd6da02ee4d9003fa0926ed74dead2a79cca9a0031f674b2e1ed3ba933a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs11_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData11_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData11_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared11

theorem _root_.D1Bound5.PairGraphPrepared11.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_11 smallPairB_11 anchorRoot
      (10^1100) smallPairClosure_11 witnesses destinations = true := by sorry



end D1Bound5
end
