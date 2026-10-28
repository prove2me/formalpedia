-- Prove2me | Theorems.Thm_D1Bound5_smallDisk_0_4_eq
-- name    : D1Bound5.smallDisk_0_4_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:31.249996+00:00
-- url     : https://prove2.me/theorems/d64ea515-c3fc-49f1-afcc-bd1a5589e8d5
-- title:
--   Small Disk 0 4 eq
-- statement:
--   Auxiliary result `smallDisk_0_4_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallQuadrupleData.lean, lines 56-57, SHA-256 83944223ca113d2d1cc1c359d4a5cef8fb9f895b6e7bf9288b74b8f7a03d8908. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000



























theorem _root_.D1Bound5.smallDisk_0_4_eq : disk 0 4 8 = smallDisk_0_4.toFinset := by sorry







































































































end D1Bound5
end
