-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_17_checked
-- name    : D1Bound5.oneSmallFourth_17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:01.666498+00:00
-- url     : https://prove2.me/theorems/7d5f9838-a89c-41c0-aa7e-c39a274f4a8c
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_12`, `oneSmallPairB_12`, `oneSmallTripleS_17`, cutoff `oneSmallTripleCutoff_17`, and root list `oneSmallDisk_300_1_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData3.lean, lines 31-34, SHA-256 712ce9ac0d1d7ce039679eee84a0208d19beae02c5a7354f5a8d0215830eb273. Project: https://github.com/tomislav-math/d1-bound5-lean

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











theorem _root_.D1Bound5.oneSmallFourth_17_checked :
    oneSmallFourthGrowthBool oneSmallPairA_12 oneSmallPairB_12 oneSmallTripleS_17
      oneSmallTripleCutoff_17 oneSmallDisk_300_1_1 = true := by sorry













































end D1Bound5
end
