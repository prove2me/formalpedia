-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_35_growth
-- name    : D1Bound5.oneSmallFourth_35_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:04:08.7596+00:00
-- url     : https://prove2.me/theorems/9a2c1113-37d7-409f-8107-6cf89e6be5ea
-- title:
--   Fourth-element norm bound for case 35
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData5.lean, lines 76-86, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83. Project: https://github.com/tomislav-math/d1-bound5-lean

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



























theorem _root_.D1Bound5.oneSmallFourth_35_growth (z : QuadInt 0 5)
    (hz : z.norm < oneSmallTripleCutoff_35)
    (ha : ∃ q, q*q = oneSmallPairA_25*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_25*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_35*z+1) :
    z.norm ≤ 4*oneSmallPairB_25.norm*oneSmallTripleS_35.norm := by sorry





























end D1Bound5
end
