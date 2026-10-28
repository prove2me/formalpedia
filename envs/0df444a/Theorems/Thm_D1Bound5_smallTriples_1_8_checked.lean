-- Prove2me | Theorems.Thm_D1Bound5_smallTriples_1_8_checked
-- name    : D1Bound5.smallTriples_1_8_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:43:57.603256+00:00
-- url     : https://prove2.me/theorems/3f42d472-dc0a-4daa-9bd2-f7cf2c82468f
-- title:
--   Small Triples 1 8 checked
-- statement:
--   Auxiliary result `smallTriples_1_8_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleData.lean, lines 315-317, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da. Project: https://github.com/tomislav-math/d1-bound5-lean

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






















































































theorem _root_.D1Bound5.smallTriples_1_8_checked :
    smallTripleClassifiedBool smallDisk_1_8 (smallTripleTable 1 8) = true := by sorry





end D1Bound5
end
