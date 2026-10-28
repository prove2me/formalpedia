-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_51_checked
-- name    : D1Bound5.oneSmallFourth_51_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:42:45.732654+00:00
-- url     : https://prove2.me/theorems/92fc630e-169b-434d-9046-44c9429abac3
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_37`, `oneSmallPairB_37`, `oneSmallTripleS_51`, cutoff `oneSmallTripleCutoff_51`, and root list `oneSmallDisk_300_1_6`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData7.lean, lines 71-74, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

























theorem _root_.D1Bound5.oneSmallFourth_51_checked :
    oneSmallFourthGrowthBool oneSmallPairA_37 oneSmallPairB_37 oneSmallTripleS_51
      oneSmallTripleCutoff_51 oneSmallDisk_300_1_6 = true := by sorry































end D1Bound5
end
