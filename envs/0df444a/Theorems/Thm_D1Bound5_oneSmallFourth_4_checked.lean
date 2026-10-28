-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_4_checked
-- name    : D1Bound5.oneSmallFourth_4_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:47:42.668613+00:00
-- url     : https://prove2.me/theorems/956cf95d-00f5-43dd-bb97-72827854e1d4
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_2`, `oneSmallPairB_2`, `oneSmallTripleS_4`, cutoff `oneSmallTripleCutoff_4`, and root list `oneSmallDisk_300_0_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData1.lean, lines 91-94, SHA-256 fbe5d4af355a60f4a8c89a4d8ea6491dec3a75d17233e2ab145f623df38cf125. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData1_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
































theorem _root_.D1Bound5.oneSmallFourth_4_checked :
    oneSmallFourthGrowthBool oneSmallPairA_2 oneSmallPairB_2 oneSmallTripleS_4
      oneSmallTripleCutoff_4 oneSmallDisk_300_0_1 = true := by sorry
























end D1Bound5
end
