-- Prove2me | Theorems.Thm_D1Bound5_seedRootDisk_0_5_eq
-- name    : D1Bound5.seedRootDisk_0_5_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:24:59.130135+00:00
-- url     : https://prove2.me/theorems/e491934e-bc07-486c-a02b-51c37add64e4
-- title:
--   Seed Root Disk 0 5 eq
-- statement:
--   Auxiliary result `seedRootDisk_0_5_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallSeedDisks.lean, lines 200-202, SHA-256 510bd0817de84470204906e29a31775f06a975fc27f5a457bad4d81a12b411eb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000


theorem _root_.D1Bound5.seedRootDisk_0_5_eq : disk 0 5 132 = seedRootDisk_0_5.toFinset := by sorry



















end D1Bound5
end
