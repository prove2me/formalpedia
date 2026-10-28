-- Prove2me | Theorems.Thm_D1Bound5_firstPair_classified_0_2
-- name    : D1Bound5.firstPair_classified_0_2
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:27:23.111543+00:00
-- url     : https://prove2.me/theorems/cd0d1a0a-4ad3-43e9-80bf-826a2776c08f
-- title:
--   First Pair classified 0 2
-- statement:
--   Auxiliary result `firstPair_classified_0_2` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairData.lean, lines 166-171, SHA-256 7313a343cb5732f1d2357b582d7fff94832a88101669f0b066de7d6ee8e698a5. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000



















































































theorem _root_.D1Bound5.firstPair_classified_0_2
    (a b : QuadInt 0 2) (hnorm : FirstPairNorms a b) (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨ firstPairCoordinates a b ∈ firstPairTable 0 2 := by sorry



























































end D1Bound5
end
