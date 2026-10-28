-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_2_growth
-- name    : D1Bound5.oneSmallFourth_2_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:33.193474+00:00
-- url     : https://prove2.me/theorems/4aa6b2d4-bc42-4d1d-b3b5-eabc4487afea
-- title:
--   Fourth-element norm bound for case 2
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData1.lean, lines 56-66, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125. Project: https://github.com/tomislav-math/d1-bound5-lean

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




















theorem _root_.D1Bound5.oneSmallFourth_2_growth (z : QuadInt 0 1)
    (hz : z.norm < oneSmallTripleCutoff_2)
    (ha : ∃ q, q*q = oneSmallPairA_0*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_0*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_2*z+1) :
    z.norm ≤ 4*oneSmallPairB_0.norm*oneSmallTripleS_2.norm := by sorry




































end D1Bound5
end
