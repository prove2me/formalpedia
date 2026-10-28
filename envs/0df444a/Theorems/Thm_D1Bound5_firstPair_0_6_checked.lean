-- Prove2me | Theorems.Thm_D1Bound5_firstPair_0_6_checked
-- name    : D1Bound5.firstPair_0_6_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:57.338989+00:00
-- url     : https://prove2.me/theorems/18d665a4-b13e-4333-a688-3f7e51c94dea
-- title:
--   First Pair 0 6 checked
-- statement:
--   Auxiliary result `firstPair_0_6_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairData.lean, lines 206-208, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

































































































theorem _root_.D1Bound5.firstPair_0_6_checked :
    firstPairClassifiedBool smallDisk_0_6 smallDisk_0_6 (firstPairTable 0 6) = true := by sorry













































end D1Bound5
end
