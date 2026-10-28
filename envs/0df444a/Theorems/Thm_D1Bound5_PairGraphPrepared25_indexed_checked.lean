-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared25_indexed_checked
-- name    : D1Bound5.PairGraphPrepared25.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:10:30.033709+00:00
-- url     : https://prove2.me/theorems/945b3926-8d94-4c32-b721-767137549dbf
-- title:
--   Pair Graph Prepared25 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared25.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure25.lean, lines 21-102, SHA-256 d76b5a372dcc2a0a86abd57001a94b86fd9580c549192fe65cf554ec752528d1. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs25_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs25_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData25_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData25_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared25

theorem _root_.D1Bound5.PairGraphPrepared25.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_25 smallPairB_25 anchorRoot
      (10^1100) smallPairClosure_25 witnesses destinations = true := by sorry



end D1Bound5
end
