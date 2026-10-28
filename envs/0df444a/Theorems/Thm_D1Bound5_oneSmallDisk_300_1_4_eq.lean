-- Prove2me | Theorems.Thm_D1Bound5_oneSmallDisk_300_1_4_eq
-- name    : D1Bound5.oneSmallDisk_300_1_4_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:54.232033+00:00
-- url     : https://prove2.me/theorems/9fa2410e-4298-4c10-9b1d-a46b15a05677
-- title:
--   One Small Disk 300 1 4 eq
-- statement:
--   Auxiliary result `oneSmallDisk_300_1_4_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallDisks.lean, lines 9313-9315, SHA-256 d3631e558f24a2c5d5c5bf3094b0a66f9d4e156f88e613285548da0e0753f985. Project: https://github.com/tomislav-math/d1-bound5-lean

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































































theorem _root_.D1Bound5.oneSmallDisk_300_1_4_eq : disk 1 4 300 = oneSmallDisk_300_1_4.toFinset := by sorry

















end D1Bound5
end
