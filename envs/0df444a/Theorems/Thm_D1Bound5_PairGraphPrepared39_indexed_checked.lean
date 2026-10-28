-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared39_indexed_checked
-- name    : D1Bound5.PairGraphPrepared39.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:23:43.380201+00:00
-- url     : https://prove2.me/theorems/f5a8e26e-a043-4436-882a-0d912cf76568
-- title:
--   Pair Graph Prepared39 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared39.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure39.lean, lines 24-123, SHA-256 f26497ef6d3cccc6278eb12c2fffdce9f33c00ccecb194296322ca7bc67f98e1. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData39_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData39_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared39

theorem _root_.D1Bound5.PairGraphPrepared39.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_39 smallPairB_39 anchorRoot
      (10^1100) smallPairClosure_39 witnesses destinations = true := by sorry



end D1Bound5
end
