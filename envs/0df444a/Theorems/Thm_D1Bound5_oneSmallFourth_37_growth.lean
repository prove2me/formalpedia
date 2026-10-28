-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_37_growth
-- name    : D1Bound5.oneSmallFourth_37_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:55:39.214924+00:00
-- url     : https://prove2.me/theorems/c267f24d-1733-42b4-bda4-92272571df72
-- title:
--   Fourth-element norm bound for case 37
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData5.lean, lines 116-126, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData5_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000









































theorem _root_.D1Bound5.oneSmallFourth_37_growth (z : QuadInt 0 6)
    (hz : z.norm < oneSmallTripleCutoff_37)
    (ha : ∃ q, q*q = oneSmallPairA_27*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_27*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_37*z+1) :
    z.norm ≤ 4*oneSmallPairB_27.norm*oneSmallTripleS_37.norm := by sorry















end D1Bound5
end
