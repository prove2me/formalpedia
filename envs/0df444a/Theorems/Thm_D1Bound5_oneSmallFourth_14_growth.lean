-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_14_growth
-- name    : D1Bound5.oneSmallFourth_14_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:03:41.924582+00:00
-- url     : https://prove2.me/theorems/f4a97205-c7cc-4c63-aaca-d47a602440ae
-- title:
--   Fourth-element norm bound for case 14
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData2.lean, lines 136-146, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData2_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
















































theorem _root_.D1Bound5.oneSmallFourth_14_growth (z : QuadInt 0 2)
    (hz : z.norm < oneSmallTripleCutoff_14)
    (ha : ∃ q, q*q = oneSmallPairA_9*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_9*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_14*z+1) :
    z.norm ≤ 4*oneSmallPairB_9.norm*oneSmallTripleS_14.norm := by sorry








end D1Bound5
end
