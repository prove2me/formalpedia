-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_12_checked
-- name    : D1Bound5.oneSmallFourth_12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:36.334825+00:00
-- url     : https://prove2.me/theorems/b11c0f36-2311-41df-b45d-2df51a61bc85
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_7`, `oneSmallPairB_7`, `oneSmallTripleS_12`, cutoff `oneSmallTripleCutoff_12`, and root list `oneSmallDisk_300_0_2`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData2.lean, lines 91-94, SHA-256 9bdd844e1a1dd93e94c0a25cded3a92f3e641f7528cfe2a1a7e6a8d500bc3593. Project: https://github.com/tomislav-math/d1-bound5-lean

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
































theorem _root_.D1Bound5.oneSmallFourth_12_checked :
    oneSmallFourthGrowthBool oneSmallPairA_7 oneSmallPairB_7 oneSmallTripleS_12
      oneSmallTripleCutoff_12 oneSmallDisk_300_0_2 = true := by sorry
























end D1Bound5
end
