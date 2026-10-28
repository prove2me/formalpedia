-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_46_growth
-- name    : D1Bound5.oneSmallFourth_46_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:59:45.940443+00:00
-- url     : https://prove2.me/theorems/98930eb8-c542-40f3-aee7-0fed9b537cb0
-- title:
--   Fourth-element norm bound for case 46
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData6.lean, lines 136-146, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData6_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
















































theorem _root_.D1Bound5.oneSmallFourth_46_growth (z : QuadInt 1 4)
    (hz : z.norm < oneSmallTripleCutoff_46)
    (ha : ∃ q, q*q = oneSmallPairA_33*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_33*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_46*z+1) :
    z.norm ≤ 4*oneSmallPairB_33.norm*oneSmallTripleS_46.norm := by sorry








end D1Bound5
end
