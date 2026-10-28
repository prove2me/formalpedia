-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourth_40_checked
-- name    : D1Bound5.oneSmallFourth_40_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:07.504375+00:00
-- url     : https://prove2.me/theorems/8740b136-2692-4c48-b875-d18179fbb9ae
-- title:
--   Finite fourth-element growth certificate
-- statement:
--   The finite fourth-element growth check succeeds for anchors `oneSmallPairA_29`, `oneSmallPairB_29`, `oneSmallTripleS_40`, cutoff `oneSmallTripleCutoff_40`, and root list `oneSmallDisk_300_1_2`. Every tested candidate below this cutoff that passes the three square conditions satisfies N(z) ≤ 4N(b)N(s).
-- source:
--   D1Bound5/OneSmallFourthData6.lean, lines 11-14, SHA-256 7aac959f93eca3ae2cb1239543f66f1845a1dfb068e2493999adf9be5e60d0a6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFourthData6_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000




theorem _root_.D1Bound5.oneSmallFourth_40_checked :
    oneSmallFourthGrowthBool oneSmallPairA_29 oneSmallPairB_29 oneSmallTripleS_40
      oneSmallTripleCutoff_40 oneSmallDisk_300_1_2 = true := by sorry




















































end D1Bound5
end
