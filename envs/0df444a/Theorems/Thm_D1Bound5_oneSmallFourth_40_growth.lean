-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_40_growth
-- name    : D1Bound5.oneSmallFourth_40_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:22:13.443965+00:00
-- url     : https://prove2.me/theorems/7bbc392c-f91b-49d1-a95f-5e4fac805305
-- title:
--   Fourth-element norm bound for case 40
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData6.lean, lines 16-26, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.oneSmallFourth_40_growth (z : QuadInt 1 2)
    (hz : z.norm < oneSmallTripleCutoff_40)
    (ha : ∃ q, q*q = oneSmallPairA_29*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_29*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_40*z+1) :
    z.norm ≤ 4*oneSmallPairB_29.norm*oneSmallTripleS_40.norm := by sorry


















































end D1Bound5
end
