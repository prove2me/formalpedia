-- Prove2me | Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_coverage_checked
-- name    : D1Bound5.PairGraphPrepared26.indexed_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:47.48681+00:00
-- url     : https://prove2.me/theorems/888ab3dd-290d-4c30-b152-c24482ffc481
-- title:
--   Pair Graph Prepared26 — indexed coverage checked
-- statement:
--   Auxiliary result `PairGraphPrepared26.indexed_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure26Coverage.lean, lines 9-12, SHA-256 eeb3d6ef9a05df7458ee97a63ec564c4bdd4fa3a476abce4a4451e9be7506e12. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_003

section
namespace D1Bound5.PairGraphPrepared26
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairGraphPrepared26.indexed_coverage_checked :
    decide (anchorRoot * anchorRoot = smallPairA_26 * smallPairB_26 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_26) = true := by sorry

end D1Bound5.PairGraphPrepared26
end
