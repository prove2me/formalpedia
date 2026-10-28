-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_26_checked
-- name    : D1Bound5.oneSmallFourth_26_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:42:34.11408+00:00
-- url     : https://prove2.me/theorems/4632ad94-8079-4e92-a311-2a3c84689624
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_20`, `oneSmallPairB_20`, `oneSmallTripleS_26`, cutoff `oneSmallTripleCutoff_26`, and root list `oneSmallDisk_300_1_1`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData4.lean, lines 51-54, SHA-256 4656cd79395a32abd53f02e684e5c5c844ce36659be817581236fc238d0b2bc4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData4_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000


















theorem _root_.D1Bound5.oneSmallFourth_26_checked :
    oneSmallFourthGrowthBool oneSmallPairA_20 oneSmallPairB_20 oneSmallTripleS_26
      oneSmallTripleCutoff_26 oneSmallDisk_300_1_1 = true := by sorry






































end D1Bound5
end
