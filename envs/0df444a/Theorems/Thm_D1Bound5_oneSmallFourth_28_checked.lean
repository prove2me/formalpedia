-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_28_checked
-- name    : D1Bound5.oneSmallFourth_28_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:45:14.575167+00:00
-- url     : https://prove2.me/theorems/cb0d5990-52aa-425b-904d-81193bd276c6
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_21`, `oneSmallPairB_21`, `oneSmallTripleS_28`, cutoff `oneSmallTripleCutoff_28`, and root list `oneSmallDisk_300_1_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData4.lean, lines 91-94, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallDisks_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallFourthData4_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
































theorem _root_.D1Bound5.oneSmallFourth_28_checked :
    oneSmallFourthGrowthBool oneSmallPairA_21 oneSmallPairB_21 oneSmallTripleS_28
      oneSmallTripleCutoff_28 oneSmallDisk_300_1_1 = true := by sorry
























end D1Bound5
end
