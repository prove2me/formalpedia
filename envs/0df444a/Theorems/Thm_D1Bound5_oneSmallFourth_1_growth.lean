-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_1_growth
-- name    : D1Bound5.oneSmallFourth_1_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:31.178583+00:00
-- url     : https://prove2.me/theorems/1cfb8801-8fe3-4702-ace8-f92146ce8e18
-- title:
--   Fourth-element norm bound for case 1
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData1.lean, lines 36-46, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125. Project: https://github.com/tomislav-math/d1-bound5-lean

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













theorem _root_.D1Bound5.oneSmallFourth_1_growth (z : QuadInt 0 1)
    (hz : z.norm < oneSmallTripleCutoff_1)
    (ha : ∃ q, q*q = oneSmallPairA_0*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_0*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_1*z+1) :
    z.norm ≤ 4*oneSmallPairB_0.norm*oneSmallTripleS_1.norm := by sorry











































end D1Bound5
end
