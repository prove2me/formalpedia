-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared24_indexed_checked
-- name    : D1Bound5.PairGraphPrepared24.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:23:45.491466+00:00
-- url     : https://prove2.me/theorems/2d41d960-4775-4b1a-a972-02489a39ab61
-- title:
--   Pair Graph Prepared24 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared24.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure24.lean, lines 23-116, SHA-256 70a9d7c7f2a7251caa1ae5a9ca44a7e950ecae9265e65a7617581d098f23360e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared24

theorem _root_.D1Bound5.PairGraphPrepared24.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_24 smallPairB_24 anchorRoot
      (10^1100) smallPairClosure_24 witnesses destinations = true := by sorry



end D1Bound5
end
