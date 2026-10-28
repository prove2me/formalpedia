-- Prove2me | Theorems.Thm_D1Bound5_smallTriple_classified_0_5
-- name    : D1Bound5.smallTriple_classified_0_5
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:47.236333+00:00
-- url     : https://prove2.me/theorems/23160edd-43a9-41a5-aebb-9d4010af9d3d
-- title:
--   Small Triple classified 0 5
-- statement:
--   Auxiliary result `smallTriple_classified_0_5` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleData.lean, lines 165-173, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000












































theorem _root_.D1Bound5.smallTriple_classified_0_5
    (t : Fin 3 → QuadInt 0 5) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ smallTripleTable 0 5 := by sorry















































end D1Bound5
end
