-- Prove2me | Theorems.Thm_D1Bound5_smallTripleClosure_7_checked
-- name    : D1Bound5.smallTripleClosure_7_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:33:45.338733+00:00
-- url     : https://prove2.me/theorems/464432c5-bfbd-4a83-bbdb-05da99c01d5c
-- title:
--   Small Triple Closure 7 checked
-- statement:
--   Auxiliary result `smallTripleClosure_7_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData7.lean, lines 136-139, SHA-256 784947cee6255504e305aae62572ff2231ec8392139ceb2d3615de8ad4f2c5f3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData7_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000











theorem _root_.D1Bound5.smallTripleClosure_7_checked :
    pairClosureBool smallTripleAnchorA_7 smallTripleAnchorB_7
      (10^80) smallTriplePairClosure_7 = true := by sorry





end D1Bound5
end
