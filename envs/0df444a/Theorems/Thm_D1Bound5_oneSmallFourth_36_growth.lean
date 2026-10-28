-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_36_growth
-- name    : D1Bound5.oneSmallFourth_36_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:55:13.740116+00:00
-- url     : https://prove2.me/theorems/dcd56f7c-236e-4cdb-be68-27b0644d53fd
-- title:
--   Fourth-element norm bound for case 36
-- statement:
--   For the specified anchors a, b and s, every element z below the stated norm cutoff for which az + 1, bz + 1 and sz + 1 are squares satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData5.lean, lines 96-106, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83. Project: https://github.com/tomislav-math/d1-bound5-lean

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


































theorem _root_.D1Bound5.oneSmallFourth_36_growth (z : QuadInt 0 5)
    (hz : z.norm < oneSmallTripleCutoff_36)
    (ha : ∃ q, q*q = oneSmallPairA_26*z+1)
    (hb : ∃ q, q*q = oneSmallPairB_26*z+1)
    (hs : ∃ q, q*q = oneSmallTripleS_36*z+1) :
    z.norm ≤ 4*oneSmallPairB_26.norm*oneSmallTripleS_36.norm := by sorry






















end D1Bound5
end
