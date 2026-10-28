-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_48_growth
-- name    : D1Bound5.oneSmallFourth_48_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:02:21.516718+00:00
-- url     : https://prove2.me/theorems/9686b3e7-1b45-4406-82cb-ce9dae00e464
-- title:
--   Fourth-element norm bound for case 48
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData7.lean, lines 16-26, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData7_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000






theorem _root_.D1Bound5.oneSmallFourth_48_growth (z : QuadInt 1 5)
    (hz : z.norm < oneSmallTripleCutoff_48)
    (ha : ∃ q, q*q = oneSmallPairA_35*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_35*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_48*z+1) :
    z.norm ≤ 4*oneSmallPairB_35.norm*oneSmallTripleS_48.norm := by sorry


















































end D1Bound5
end
