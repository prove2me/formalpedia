-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_7_growth
-- name    : D1Bound5.oneSmallFourth_7_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:35.385983+00:00
-- url     : https://prove2.me/theorems/9fe2a2a1-94f9-4a2a-b431-d4b6ac404ab3
-- title:
--   Fourth-element norm bound for case 7
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData1.lean, lines 156-166, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData1_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000























































theorem _root_.D1Bound5.oneSmallFourth_7_growth (z : QuadInt 0 1)
    (hz : z.norm < oneSmallTripleCutoff_7)
    (ha : ∃ q, q*q = oneSmallPairA_4*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_4*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_7*z+1) :
    z.norm ≤ 4*oneSmallPairB_4.norm*oneSmallTripleS_7.norm := by sorry

end D1Bound5
end
