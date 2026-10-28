-- Prove2me | Theorems.Thm_D1Bound5_firstPairTable_1_6_orbits
-- name    : D1Bound5.firstPairTable_1_6_orbits
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:42:51.209441+00:00
-- url     : https://prove2.me/theorems/6c7075cf-544a-41fc-a15a-0317b3f44436
-- title:
--   First Pair Table 1 6 orbits
-- statement:
--   Auxiliary result `firstPairTable_1_6_orbits` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairData.lean, lines 147-149, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000











































































theorem _root_.D1Bound5.firstPairTable_1_6_orbits :
    firstPairs_1_6.toFinset = firstPairRepresentatives_1_6.biUnion (firstPairOrbit 1) := by sorry



































































end D1Bound5
end
