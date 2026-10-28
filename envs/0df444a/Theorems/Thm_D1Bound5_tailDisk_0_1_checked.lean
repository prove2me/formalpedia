-- Prove2me | Theorems.Thm_D1Bound5_tailDisk_0_1_checked
-- name    : D1Bound5.tailDisk_0_1_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:33.538418+00:00
-- url     : https://prove2.me/theorems/d3c90774-e082-40e1-a29f-1377a3f62cef
-- title:
--   Tail Disk 0 1 checked
-- statement:
--   No external execution or native-evaluation axiom is used.
-- source:
--   D1Bound5/SmallTailData0_1.lean, lines 14-16, SHA-256 e8193c82da9fe118ab3eb160cf6f8da07be08bcc7943ff257aee829c26a5ca2e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallTailData0_1_Definitions
import Definitions.Def_D1Bound5_SmallTailExplicit_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000






theorem _root_.D1Bound5.tailDisk_0_1_checked : tailListBool tailDisk_0_1 = true := by sorry



end D1Bound5
end
