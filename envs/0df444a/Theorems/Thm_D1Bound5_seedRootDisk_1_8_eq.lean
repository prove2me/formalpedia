-- Prove2me | Theorems.Thm_D1Bound5_seedRootDisk_1_8_eq
-- name    : D1Bound5.seedRootDisk_1_8_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:25:25.567786+00:00
-- url     : https://prove2.me/theorems/1ea8d76e-6515-430f-a61c-b65fec304a96
-- title:
--   Seed Root Disk 1 8 eq
-- statement:
--   Auxiliary result `seedRootDisk_1_8_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallSeedDisks.lean, lines 1372-1374, SHA-256 510bd0817de84470204906e29a31775f06a975fc27f5a457bad4d81a12b411eb. Project: https://github.com/tomislav-math/d1-bound5-lean

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




















theorem _root_.D1Bound5.seedRootDisk_1_8_eq : disk 1 8 132 = seedRootDisk_1_8.toFinset := by sorry

end D1Bound5
end
