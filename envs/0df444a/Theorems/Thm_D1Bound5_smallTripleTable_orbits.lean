-- Prove2me | Theorems.Thm_D1Bound5_smallTripleTable_orbits
-- name    : D1Bound5.smallTripleTable_orbits
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:33:06.279584+00:00
-- url     : https://prove2.me/theorems/d97d3575-a25c-4f72-bd84-91bc14ed1516
-- title:
--   Small Triple Table orbits
-- statement:
--   Exact agreement between the explicit 24 triples and the ten manuscript orbits. The half-integral models use ω=(1+sqrt(-d))/2.
-- source:
--   D1Bound5/SmallTripleData.lean, lines 69-76, SHA-256 d79644481c842f2a40b2f5554666f54fa185f12915c38d31e4f1b24ec16844da. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000



















theorem _root_.D1Bound5.smallTripleTable_orbits :
    smallTriples_0_1.toFinset = smallTripleRepresentatives_0_1.biUnion (smallTripleOrbit 0) ∧
    smallTriples_0_2.toFinset = smallTripleRepresentatives_0_2.biUnion (smallTripleOrbit 0) ∧
    smallTriples_1_1.toFinset = smallTripleRepresentatives_1_1.biUnion (smallTripleOrbit 1) ∧
    smallTriples_1_2.toFinset = smallTripleRepresentatives_1_2.biUnion (smallTripleOrbit 1) := by sorry









































































end D1Bound5
end
