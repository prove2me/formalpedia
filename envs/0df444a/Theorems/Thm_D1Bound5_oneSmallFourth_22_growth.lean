-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_22_growth
-- name    : D1Bound5.oneSmallFourth_22_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:58:13.704082+00:00
-- url     : https://prove2.me/theorems/8aa6865f-f739-4c77-b78d-0f60f3dee963
-- title:
--   Fourth-element norm bound for case 22
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData3.lean, lines 136-146, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273. Project: https://github.com/tomislav-math/d1-bound5-lean

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
















































theorem _root_.D1Bound5.oneSmallFourth_22_growth (z : QuadInt 1 1)
    (hz : z.norm < oneSmallTripleCutoff_22)
    (ha : ∃ q, q*q = oneSmallPairA_16*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_16*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_22*z+1) :
    z.norm ≤ 4*oneSmallPairB_16.norm*oneSmallTripleS_22.norm := by sorry








end D1Bound5
end
