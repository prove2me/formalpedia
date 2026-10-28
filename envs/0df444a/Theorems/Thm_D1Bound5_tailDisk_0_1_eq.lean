-- Prove2me | Theorems.Thm_D1Bound5_tailDisk_0_1_eq
-- name    : D1Bound5.tailDisk_0_1_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:39.388475+00:00
-- url     : https://prove2.me/theorems/b369acfa-a9f1-4536-bf0e-2c1320175d77
-- title:
--   Tail Disk 0 1 eq
-- statement:
--   Kernel-checked equality with the proved exhaustive disk enumeration.
-- source:
--   D1Bound5/SmallTailData0_1.lean, lines 10-12, SHA-256 e8193c82da9fe118ab3eb160cf6f8da07be08bcc7943ff257aee829c26a5ca2e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTailData0_1_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000




theorem _root_.D1Bound5.tailDisk_0_1_eq : disk 0 1 15 = tailDisk_0_1.toFinset := by sorry





end D1Bound5
end
