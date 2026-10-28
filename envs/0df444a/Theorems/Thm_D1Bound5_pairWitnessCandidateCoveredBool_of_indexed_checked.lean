-- Prove2me | Theorems.Thm_D1Bound5_pairWitnessCandidateCoveredBool_of_indexed_checked
-- name    : D1Bound5.pairWitnessCandidateCoveredBool_of_indexed_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:43.178983+00:00
-- url     : https://prove2.me/theorems/1c6056d6-af6c-468a-a4d7-c2c51c4daae0
-- title:
--   Pair Witness Candidate Covered Bool of indexed checked
-- statement:
--   Every accepted indexed candidate satisfies the original membership checker. In-range lookup is required by `getElem? = some w` itself.
-- source:
--   D1Bound5/PairClosureIndexedWitness.lean, lines 48-64, SHA-256 396e39b992bc9611aabcfcda13356692e98676409381a756555e84104fe22420. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.pairWitnessCandidateCoveredBool_of_indexed_checked {tau nu : ℤ}
    (bound : ℤ) (vertices : List (QuadInt tau nu)) (w : QuadInt tau nu)
    (destination : Option Nat)
    (hcheck : pairIndexedCandidateCoveredBool bound vertices w destination = true) :
    pairWitnessCandidateCoveredBool bound vertices w = true := by sorry









end D1Bound5
end
