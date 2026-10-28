-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared31_indexed_checked
-- name    : D1Bound5.PairGraphPrepared31.indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:02:31.92935+00:00
-- url     : https://prove2.me/theorems/1f7c116d-722f-4ad5-9d32-240376b7ed13
-- title:
--   Pair Graph Prepared31 — indexed checked
-- statement:
--   Auxiliary result `PairGraphPrepared31.indexed_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure31.lean, lines 10-13, SHA-256 158ad2bc2984a2c5ba3dac1285f2ee71d25d8138367e6f04ba67264e3cc71dca. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData31_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared31

theorem _root_.D1Bound5.PairGraphPrepared31.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_31 smallPairB_31 anchorRoot
      (10^1100) smallPairClosure_31 witnesses destinations = true := by sorry



end D1Bound5
end
