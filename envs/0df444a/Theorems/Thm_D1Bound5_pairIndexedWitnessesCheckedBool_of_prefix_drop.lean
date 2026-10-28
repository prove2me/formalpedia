-- Prove2me | Theorems.Thm_D1Bound5_pairIndexedWitnessesCheckedBool_of_prefix_drop
-- name    : D1Bound5.pairIndexedWitnessesCheckedBool_of_prefix_drop
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:51:14.491981+00:00
-- url     : https://prove2.me/theorems/db0e1afe-1aa5-4f20-b1a1-c2eb7a315d3d
-- title:
--   Pair Indexed Witnesses Checked Bool of prefix drop
-- statement:
--   Assemble already checked prefixes without evaluating their arithmetic again.
-- source:
--   D1Bound5/PairClosureIndexedChunks.lean, lines 47-58, SHA-256 29488713ab2248b4e724873977d8278f8e302994a76dfd2d1c47bf8aa3e6e226. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions

section
namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.pairIndexedWitnessesCheckedBool_of_prefix_drop {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (n : ℕ) (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat))
    (hprefix : pairIndexedWitnessesPrefixBool a b r0 bound vertices n
      witnesses destinations = true)
    (htail : pairIndexedWitnessesCheckedBool a b r0 bound vertices
      (witnesses.drop n) (destinations.drop n) = true) :
    pairIndexedWitnessesCheckedBool a b r0 bound vertices witnesses destinations = true := by sorry





end D1Bound5
end
