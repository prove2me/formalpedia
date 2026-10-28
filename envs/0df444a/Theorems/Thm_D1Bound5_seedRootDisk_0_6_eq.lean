-- Prove2me | Theorems.Thm_D1Bound5_seedRootDisk_0_6_eq
-- name    : D1Bound5.seedRootDisk_0_6_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:24:46.481899+00:00
-- url     : https://prove2.me/theorems/a3269609-01db-4984-8c61-f64ee7ffd6fb
-- title:
--   Seed Root Disk 0 6 eq
-- statement:
--   Auxiliary result `seedRootDisk_0_6_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallSeedDisks.lean, lines 377-379, SHA-256 510bd0817de84470204906e29a31775f06a975fc27f5a457bad4d81a12b411eb. Project: https://github.com/tomislav-math/d1-bound5-lean

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





theorem _root_.D1Bound5.seedRootDisk_0_6_eq : disk 0 6 132 = seedRootDisk_0_6.toFinset := by sorry
















end D1Bound5
end
