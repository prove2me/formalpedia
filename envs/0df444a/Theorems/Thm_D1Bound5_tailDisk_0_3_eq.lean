-- Prove2me | Theorems.Thm_D1Bound5_tailDisk_0_3_eq
-- name    : D1Bound5.tailDisk_0_3_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:04:10.822984+00:00
-- url     : https://prove2.me/theorems/f4d0499b-2cbc-40e5-b196-a43c58a2ac6c
-- title:
--   Tail Disk 0 3 eq
-- statement:
--   Kernel-checked equality with the proved exhaustive disk enumeration.
-- source:
--   D1Bound5/SmallTailAllData.lean, lines 28-30, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SmallTailAllData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000












theorem _root_.D1Bound5.tailDisk_0_3_eq : disk 0 3 15 = tailDisk_0_3.toFinset := by sorry























































































































































































































end D1Bound5
end
