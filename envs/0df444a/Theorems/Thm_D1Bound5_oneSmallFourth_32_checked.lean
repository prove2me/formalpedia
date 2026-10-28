-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_32_checked
-- name    : D1Bound5.oneSmallFourth_32_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:06.444673+00:00
-- url     : https://prove2.me/theorems/b34c374a-dc98-4525-81bf-dd72fd1180ad
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_23`, `oneSmallPairB_23`, `oneSmallTripleS_32`, cutoff `oneSmallTripleCutoff_32`, and root list `oneSmallDisk_300_1_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData5.lean, lines 11-14, SHA-256 5c4d3dbb0b4b211a60602b6817a3d1f01003ce7efb46fbb3cb9a1abbd8a8cf83. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData5_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000




theorem _root_.D1Bound5.oneSmallFourth_32_checked :
    oneSmallFourthGrowthBool oneSmallPairA_23 oneSmallPairB_23 oneSmallTripleS_32
      oneSmallTripleCutoff_32 oneSmallDisk_300_1_1 = true := by sorry




















































end D1Bound5
end
