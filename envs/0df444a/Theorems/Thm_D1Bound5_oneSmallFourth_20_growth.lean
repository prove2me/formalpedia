-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_20_growth
-- name    : D1Bound5.oneSmallFourth_20_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:04:08.081928+00:00
-- url     : https://prove2.me/theorems/8768a629-3b64-42dc-b8f6-67efdf7c5f00
-- title:
--   Fourth-element norm bound for case 20
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData3.lean, lines 96-106, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273. Project: https://github.com/tomislav-math/d1-bound5-lean

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


































theorem _root_.D1Bound5.oneSmallFourth_20_growth (z : QuadInt 1 1)
    (hz : z.norm < oneSmallTripleCutoff_20)
    (ha : ∃ q, q*q = oneSmallPairA_15*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_15*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_20*z+1) :
    z.norm ≤ 4*oneSmallPairB_15.norm*oneSmallTripleS_20.norm := by sorry






















end D1Bound5
end
