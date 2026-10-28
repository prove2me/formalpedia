-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_checked
-- name    : D1Bound5.PairGraphPrepared26.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:15:14.01044+00:00
-- url     : https://prove2.me/theorems/5cc79bc4-4566-4ae1-8e54-8bcddb71617b
-- title:
--   Pair Graph Prepared26 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared26.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure26.lean, lines 21-126, SHA-256 82ec229ea101e9f26ad2b2727eea85dc7250fbd1b9062f6e8a8c1ff4a2ee7cf0. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared26

theorem _root_.D1Bound5.PairGraphPrepared26.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 witnesses destinations = true := by sorry



end D1Bound5
end
