-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_23_growth
-- name    : D1Bound5.oneSmallFourth_23_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:58:12.427906+00:00
-- url     : https://prove2.me/theorems/c7dce1a9-c3b5-479c-b509-fd612a143d74
-- title:
--   Fourth-element norm bound for case 23
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData3.lean, lines 156-166, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData3_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000























































theorem _root_.D1Bound5.oneSmallFourth_23_growth (z : QuadInt 1 1)
    (hz : z.norm < oneSmallTripleCutoff_23)
    (ha : ∃ q, q*q = oneSmallPairA_17*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_17*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_23*z+1) :
    z.norm ≤ 4*oneSmallPairB_17.norm*oneSmallTripleS_23.norm := by sorry

end D1Bound5
end
