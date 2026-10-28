-- Prove2me | Theorems.Thm_D1Bound5_seedRootDisk_1_1_eq
-- name    : D1Bound5.seedRootDisk_1_1_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:45:09.69123+00:00
-- url     : https://prove2.me/theorems/82a7c48a-9521-47e6-b904-4fc97797d4b7
-- title:
--   Seed Root Disk 1 1 eq
-- statement:
--   Auxiliary result `seedRootDisk_1_1_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairSeedDisks.lean, lines 1218-1220, SHA-256 78505b817d0fd58b324eb977c7c891cc24704cb83dce618764d353027caf26bb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000








theorem _root_.D1Bound5.seedRootDisk_1_1_eq : disk 1 1 132 = seedRootDisk_1_1.toFinset := by sorry




end D1Bound5
end
