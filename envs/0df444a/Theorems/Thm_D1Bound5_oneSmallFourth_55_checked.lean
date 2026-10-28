-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_55_checked
-- name    : D1Bound5.oneSmallFourth_55_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:07.054871+00:00
-- url     : https://prove2.me/theorems/14e4fa33-102b-492c-a0b5-ecf2de9e92b9
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_39`, `oneSmallPairB_39`, `oneSmallTripleS_55`, cutoff `oneSmallTripleCutoff_55`, and root list `oneSmallDisk_300_0_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData7.lean, lines 151-154, SHA-256 0b8e884d1ce5df34ee0ab1ba66c3c86b9f949af320f3ddb5bfe6edeaf2cec83c. Project: https://github.com/tomislav-math/d1-bound5-lean

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





















































theorem _root_.D1Bound5.oneSmallFourth_55_checked :
    oneSmallFourthGrowthBool oneSmallPairA_39 oneSmallPairB_39 oneSmallTripleS_55
      oneSmallTripleCutoff_55 oneSmallDisk_300_0_1 = true := by sorry



end D1Bound5
end
