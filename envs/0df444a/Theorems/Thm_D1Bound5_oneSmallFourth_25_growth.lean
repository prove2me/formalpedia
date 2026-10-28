-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_25_growth
-- name    : D1Bound5.oneSmallFourth_25_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:36.162785+00:00
-- url     : https://prove2.me/theorems/25897148-98af-4c42-872a-7998356de922
-- title:
--   Fourth-element norm bound for case 25
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData4.lean, lines 36-46, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData4_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000













theorem _root_.D1Bound5.oneSmallFourth_25_growth (z : QuadInt 1 1)
    (hz : z.norm < oneSmallTripleCutoff_25)
    (ha : ∃ q, q*q = oneSmallPairA_19*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_19*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_25*z+1) :
    z.norm ≤ 4*oneSmallPairB_19.norm*oneSmallTripleS_25.norm := by sorry











































end D1Bound5
end
