-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared27_indexed_checked
-- name    : D1Bound5.PairGraphPrepared27.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:02:51.50897+00:00
-- url     : https://prove2.me/theorems/c3b43b81-a977-4f6f-875a-4986263cc220
-- title:
--   Pair Graph Prepared27 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared27.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure27.lean, lines 10-13, SHA-256 d077587b50fdf4bae44e9ac3733a891d809f3bd20c8ce63e05c8cfa6313203f6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData27_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData27_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared27

theorem _root_.D1Bound5.PairGraphPrepared27.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_27 smallPairB_27 anchorRoot
      (10^1100) smallPairClosure_27 witnesses destinations = true := by sorry



end D1Bound5
end
