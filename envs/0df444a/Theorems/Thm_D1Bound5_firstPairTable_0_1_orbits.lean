-- Prove2me | Theorems.Thm_D1Bound5_firstPairTable_0_1_orbits
-- name    : D1Bound5.firstPairTable_0_1_orbits
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:43:03.63132+00:00
-- url     : https://prove2.me/theorems/da121f83-4d0c-4db5-a05b-9723f709c746
-- title:
--   First Pair Table 0 1 orbits
-- statement:
--   Auxiliary result `firstPairTable_0_1_orbits` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairData.lean, lines 84-86, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5. Project: https://github.com/tomislav-math/d1-bound5-lean

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







































theorem _root_.D1Bound5.firstPairTable_0_1_orbits :
    firstPairs_0_1.toFinset = firstPairRepresentatives_0_1.biUnion (firstPairOrbit 0) := by sorry







































































































end D1Bound5
end
