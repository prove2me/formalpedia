-- Prove2me | Theorems.Thm_D1Bound5_smallTriples_1_3_checked
-- name    : D1Bound5.smallTriples_1_3_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:49:01.657621+00:00
-- url     : https://prove2.me/theorems/8ad99ef4-f7b4-418f-ae90-9a911b787fcb
-- title:
--   Small Triples 1 3 checked
-- statement:
--   Auxiliary result `smallTriples_1_3_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleData.lean, lines 245-247, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000


































































theorem _root_.D1Bound5.smallTriples_1_3_checked :
    smallTripleClassifiedBool smallDisk_1_3 (smallTripleTable 1 3) = true := by sorry

























end D1Bound5
end
