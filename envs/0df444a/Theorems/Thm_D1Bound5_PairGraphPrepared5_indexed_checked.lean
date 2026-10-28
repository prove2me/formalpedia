-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_checked
-- name    : D1Bound5.PairGraphPrepared5.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:31:43.890952+00:00
-- url     : https://prove2.me/theorems/72abd6f6-c0f4-4905-b89a-8eaebc0ead11
-- title:
--   Pair Graph Prepared5 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared5.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure5.lean, lines 23-116, SHA-256 0f8111305d0490b3c824482862d51cdfc5655c7e09439363620d0f1812d03c5d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData5_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData5_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared5

theorem _root_.D1Bound5.PairGraphPrepared5.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 witnesses destinations = true := by sorry



end D1Bound5
end
