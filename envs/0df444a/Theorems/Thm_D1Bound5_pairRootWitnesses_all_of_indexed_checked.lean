-- Prove2me | Theorems.Thm_D1Bound5_pairRootWitnesses_all_of_indexed_checked
-- name    : D1Bound5.pairRootWitnesses_all_of_indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:41.53824+00:00
-- url     : https://prove2.me/theorems/59559d7e-2ba2-43ea-9744-cf01d5e2f2b3
-- title:
--   Pair Root Witnesses all of indexed checked
-- statement:
--   The lockstep checker validates every witness in the original list.
-- source:
--   D1Bound5/PairClosureIndexedWitness.lean, lines 82-100, SHA-256 396e39b992bc9611aabcfcda13356692e98676409381a756555e84104fe22420. Project: https://github.com/tomislav-math/d1-bound5-lean

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














theorem _root_.D1Bound5.pairRootWitnesses_all_of_indexed_checked {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat))
    (hcheck : pairIndexedWitnessesCheckedBool a b r0 bound vertices witnesses destinations = true) :
    witnesses.all (pairRootWitnessCheckedBool a b r0 bound vertices) = true := by sorry





end D1Bound5
end
