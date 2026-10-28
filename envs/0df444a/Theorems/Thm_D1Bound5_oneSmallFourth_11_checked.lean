-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_11_checked
-- name    : D1Bound5.oneSmallFourth_11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:45:13.850334+00:00
-- url     : https://prove2.me/theorems/6cff6e77-f984-472a-b65b-4b2534626ee0
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_7`, `oneSmallPairB_7`, `oneSmallTripleS_11`, cutoff `oneSmallTripleCutoff_11`, and root list `oneSmallDisk_300_0_2`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData2.lean, lines 71-74, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593. Project: https://github.com/tomislav-math/d1-bound5-lean

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

























theorem _root_.D1Bound5.oneSmallFourth_11_checked :
    oneSmallFourthGrowthBool oneSmallPairA_7 oneSmallPairB_7 oneSmallTripleS_11
      oneSmallTripleCutoff_11 oneSmallDisk_300_0_2 = true := by sorry































end D1Bound5
end
