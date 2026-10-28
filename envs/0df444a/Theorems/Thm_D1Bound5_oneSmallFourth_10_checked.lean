-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_10_checked
-- name    : D1Bound5.oneSmallFourth_10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:02.607625+00:00
-- url     : https://prove2.me/theorems/fefd3765-eaf5-4639-83db-ae21002128a1
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_6`, `oneSmallPairB_6`, `oneSmallTripleS_10`, cutoff `oneSmallTripleCutoff_10`, and root list `oneSmallDisk_300_0_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData2.lean, lines 51-54, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593. Project: https://github.com/tomislav-math/d1-bound5-lean

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


















theorem _root_.D1Bound5.oneSmallFourth_10_checked :
    oneSmallFourthGrowthBool oneSmallPairA_6 oneSmallPairB_6 oneSmallTripleS_10
      oneSmallTripleCutoff_10 oneSmallDisk_300_0_1 = true := by sorry






































end D1Bound5
end
