-- Prove2me | Theorems.Thm_D1Bound5_oneSmallDisk_224_0_2_eq
-- name    : D1Bound5.oneSmallDisk_224_0_2_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:44:57.683267+00:00
-- url     : https://prove2.me/theorems/9a6b948b-e351-49a5-80f0-a1736f5d520b
-- title:
--   One Small Disk 224 0 2 eq
-- statement:
--   Auxiliary result `oneSmallDisk_224_0_2_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallDisks.lean, lines 2165-2167, SHA-256 d3631e558f24a2c5d5c5bf3094b0a66f9d4e156f88e613285548da0e0753f985. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_OneSmallDisks_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000











theorem _root_.D1Bound5.oneSmallDisk_224_0_2_eq : disk 0 2 224 = oneSmallDisk_224_0_2.toFinset := by sorry





































































end D1Bound5
end
