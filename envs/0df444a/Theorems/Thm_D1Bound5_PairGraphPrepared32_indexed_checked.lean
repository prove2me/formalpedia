-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared32_indexed_checked
-- name    : D1Bound5.PairGraphPrepared32.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:02:32.691788+00:00
-- url     : https://prove2.me/theorems/f8fca8c7-3fd4-4ebb-814c-6d36f86f8fea
-- title:
--   Pair Graph Prepared32 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared32.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure32.lean, lines 10-13, SHA-256 d81733301ce0970cad0d6399ce480fe28c4050506f7914c71497601099e30860. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs32_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData32_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared32

theorem _root_.D1Bound5.PairGraphPrepared32.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_32 smallPairB_32 anchorRoot
      (10^1100) smallPairClosure_32 witnesses destinations = true := by sorry



end D1Bound5
end
