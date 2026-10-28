-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_50_checked
-- name    : D1Bound5.oneSmallFourth_50_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:42:37.078302+00:00
-- url     : https://prove2.me/theorems/7e49395a-6203-4c80-9438-ab7135e67a2b
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_36`, `oneSmallPairB_36`, `oneSmallTripleS_50`, cutoff `oneSmallTripleCutoff_50`, and root list `oneSmallDisk_300_1_5`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData7.lean, lines 51-54, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData7_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000


















theorem _root_.D1Bound5.oneSmallFourth_50_checked :
    oneSmallFourthGrowthBool oneSmallPairA_36 oneSmallPairB_36 oneSmallTripleS_50
      oneSmallTripleCutoff_50 oneSmallDisk_300_1_5 = true := by sorry






































end D1Bound5
end
