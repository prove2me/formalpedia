-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_checked
-- name    : D1Bound5.PairGraphPrepared12.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:00:38.918873+00:00
-- url     : https://prove2.me/theorems/62eec6be-f3e2-4a38-b272-94dfe84d4430
-- title:
--   Pair Graph Prepared12 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared12.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure12.lean, lines 15-72, SHA-256 c9bc50e1b25d7ad0caa0e149d8113ce4803c9e520fc7dee649f6e12e1acf6986. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData12_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared12

theorem _root_.D1Bound5.PairGraphPrepared12.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 witnesses destinations = true := by sorry



end D1Bound5
end
