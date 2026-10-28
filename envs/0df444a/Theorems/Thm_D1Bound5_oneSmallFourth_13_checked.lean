-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_13_checked
-- name    : D1Bound5.oneSmallFourth_13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:42:39.634626+00:00
-- url     : https://prove2.me/theorems/674f1b37-714c-49d7-b3a0-2b07efe99a26
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_8`, `oneSmallPairB_8`, `oneSmallTripleS_13`, cutoff `oneSmallTripleCutoff_13`, and root list `oneSmallDisk_300_0_2`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData2.lean, lines 111-114, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData2_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000







































theorem _root_.D1Bound5.oneSmallFourth_13_checked :
    oneSmallFourthGrowthBool oneSmallPairA_8 oneSmallPairB_8 oneSmallTripleS_13
      oneSmallTripleCutoff_13 oneSmallDisk_300_0_2 = true := by sorry

















end D1Bound5
end
