-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_30_checked
-- name    : D1Bound5.oneSmallFourth_30_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:11.20038+00:00
-- url     : https://prove2.me/theorems/8e379f2b-9e89-490a-a681-08508a5b3d80
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_22`, `oneSmallPairB_22`, `oneSmallTripleS_30`, cutoff `oneSmallTripleCutoff_30`, and root list `oneSmallDisk_300_1_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData4.lean, lines 131-134, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000














































theorem _root_.D1Bound5.oneSmallFourth_30_checked :
    oneSmallFourthGrowthBool oneSmallPairA_22 oneSmallPairB_22 oneSmallTripleS_30
      oneSmallTripleCutoff_30 oneSmallDisk_300_1_1 = true := by sorry










end D1Bound5
end
