-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_47_growth
-- name    : D1Bound5.oneSmallFourth_47_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:04:34.427989+00:00
-- url     : https://prove2.me/theorems/bdb2359c-c696-4e85-a725-6f53185ae7ba
-- title:
--   Fourth-element norm bound for case 47
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData6.lean, lines 156-166, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6. Project: https://github.com/tomislav-math/d1-bound5-lean

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























































theorem _root_.D1Bound5.oneSmallFourth_47_growth (z : QuadInt 1 4)
    (hz : z.norm < oneSmallTripleCutoff_47)
    (ha : ∃ q, q*q = oneSmallPairA_34*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_34*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_47*z+1) :
    z.norm ≤ 4*oneSmallPairB_34.norm*oneSmallTripleS_47.norm := by sorry

end D1Bound5
end
