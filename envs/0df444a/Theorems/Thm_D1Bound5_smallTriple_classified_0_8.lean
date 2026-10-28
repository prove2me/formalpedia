-- Prove2me | Theorems.Thm_D1Bound5_smallTriple_classified_0_8
-- name    : D1Bound5.smallTriple_classified_0_8
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:22:23.468131+00:00
-- url     : https://prove2.me/theorems/38873b83-415a-4884-a1c7-9815abb6a77c
-- title:
--   Small Triple classified 0 8
-- statement:
--   Auxiliary result `smallTriple_classified_0_8` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleData.lean, lines 207-215, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da. Project: https://github.com/tomislav-math/d1-bound5-lean

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
























































theorem _root_.D1Bound5.smallTriple_classified_0_8
    (t : Fin 3 → QuadInt 0 8) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ smallTripleTable 0 8 := by sorry



































end D1Bound5
end
