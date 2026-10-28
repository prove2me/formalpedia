-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_44_growth
-- name    : D1Bound5.oneSmallFourth_44_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:25:14.553655+00:00
-- url     : https://prove2.me/theorems/d550f7b2-82f2-43d5-914b-a68cc08f75c9
-- title:
--   Fourth-element norm bound for case 44
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData6.lean, lines 96-106, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


































theorem _root_.D1Bound5.oneSmallFourth_44_growth (z : QuadInt 1 3)
    (hz : z.norm < oneSmallTripleCutoff_44)
    (ha : ∃ q, q*q = oneSmallPairA_32*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_32*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_44*z+1) :
    z.norm ≤ 4*oneSmallPairB_32.norm*oneSmallTripleS_44.norm := by sorry






















end D1Bound5
end
