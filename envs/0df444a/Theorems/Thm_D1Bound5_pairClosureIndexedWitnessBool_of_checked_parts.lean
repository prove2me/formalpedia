-- Prove2me | Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts
-- name    : D1Bound5.pairClosureIndexedWitnessBool_of_checked_parts
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:00:16.298236+00:00
-- url     : https://prove2.me/theorems/303591fa-dce3-46a4-9a3c-426d0c24de64
-- title:
--   Pair Closure Indexed Witness Bool of checked parts
-- statement:
--   Ordered coverage and the anchor-root equation remain separate mandatory checks when the mutation-witness computation is partitioned.
-- source:
--   D1Bound5/PairClosureIndexedChunks.lean, lines 91-102, SHA-256 29488713ab2248b4e724873977d8278f8e302994a76dfd2d1c47bf8aa3e6e226. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.pairClosureIndexedWitnessBool_of_checked_parts {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat))
    (hcoverage : decide (r0 * r0 = a * b + 1 ∧
      witnesses.map PairRootWitness.vertex = vertices) = true)
    (hwitnesses : pairIndexedWitnessesCheckedBool a b r0 bound vertices
      witnesses destinations = true) :
    pairClosureIndexedWitnessBool a b r0 bound vertices witnesses destinations = true := by sorry

end D1Bound5
end
