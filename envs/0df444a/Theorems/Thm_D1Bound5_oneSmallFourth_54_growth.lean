-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_54_growth
-- name    : D1Bound5.oneSmallFourth_54_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:45.998706+00:00
-- url     : https://prove2.me/theorems/287ff665-e349-4660-9453-bd9e5a495c63
-- title:
--   Fourth-element norm bound for case 54
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData7.lean, lines 136-146, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallFourthData7_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
















































theorem _root_.D1Bound5.oneSmallFourth_54_growth (z : QuadInt 0 1)
    (hz : z.norm < oneSmallTripleCutoff_54)
    (ha : ∃ q, q*q = oneSmallPairA_38*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_38*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_54*z+1) :
    z.norm ≤ 4*oneSmallPairB_38.norm*oneSmallTripleS_54.norm := by sorry








end D1Bound5
end
