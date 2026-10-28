-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_22_checked
-- name    : D1Bound5.oneSmallFourth_22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:11.768155+00:00
-- url     : https://prove2.me/theorems/bb2c1af3-3905-4db9-9601-c561f6360de9
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_16`, `oneSmallPairB_16`, `oneSmallTripleS_22`, cutoff `oneSmallTripleCutoff_22`, and root list `oneSmallDisk_300_1_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData3.lean, lines 131-134, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData3_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000














































theorem _root_.D1Bound5.oneSmallFourth_22_checked :
    oneSmallFourthGrowthBool oneSmallPairA_16 oneSmallPairB_16 oneSmallTripleS_22
      oneSmallTripleCutoff_22 oneSmallDisk_300_1_1 = true := by sorry










end D1Bound5
end
