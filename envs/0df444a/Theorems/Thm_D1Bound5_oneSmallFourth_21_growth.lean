-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_21_growth
-- name    : D1Bound5.oneSmallFourth_21_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:59:11.461865+00:00
-- url     : https://prove2.me/theorems/4ced66b7-3051-4bd2-928b-8f45b0895f48
-- title:
--   Fourth-element norm bound for case 21
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData3.lean, lines 116-126, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273. Project: https://github.com/tomislav-math/d1-bound5-lean

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









































theorem _root_.D1Bound5.oneSmallFourth_21_growth (z : QuadInt 1 1)
    (hz : z.norm < oneSmallTripleCutoff_21)
    (ha : ∃ q, q*q = oneSmallPairA_16*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_16*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_21*z+1) :
    z.norm ≤ 4*oneSmallPairB_16.norm*oneSmallTripleS_21.norm := by sorry















end D1Bound5
end
