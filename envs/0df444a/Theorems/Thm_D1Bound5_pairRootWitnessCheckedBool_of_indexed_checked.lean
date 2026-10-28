-- Prove2me | Theorems.Thm_D1Bound5_pairRootWitnessCheckedBool_of_indexed_checked
-- name    : D1Bound5.pairRootWitnessCheckedBool_of_indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:48.392802+00:00
-- url     : https://prove2.me/theorems/3a532ea2-4979-4f90-a377-e1e18a0878a6
-- title:
--   Pair Root Witness Checked Bool of indexed checked
-- statement:
--   Indexed checking implies the previously accepted two-mutation witness check, retaining exactly its root equations and sign coverage.
-- source:
--   D1Bound5/PairClosureIndexedWitness.lean, lines 66-80, SHA-256 396e39b992bc9611aabcfcda13356692e98676409381a756555e84104fe22420. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions

section
namespace D1Bound5
open QuadInt












theorem _root_.D1Bound5.pairRootWitnessCheckedBool_of_indexed_checked {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (w : PairRootWitness tau nu) (destinations : Option Nat × Option Nat)
    (hcheck : pairIndexedRootWitnessCheckedBool a b r0 bound vertices w destinations = true) :
    pairRootWitnessCheckedBool a b r0 bound vertices w = true := by sorry







end D1Bound5
end
