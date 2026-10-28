-- Prove2me | Theorems.Thm_D1Bound5_pairIndexedWitnessesPrefixBool_add
-- name    : D1Bound5.pairIndexedWitnessesPrefixBool_add
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:53.202992+00:00
-- url     : https://prove2.me/theorems/e1ee040a-47fd-43d7-bb53-4c7eb2b7212d
-- title:
--   Indexed mutation-closure certificate
-- statement:
--   the indexed closure certificate succeeds for at most `(m + n)` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `bound`. Join two finite prefixes while preserving global destination indices.
-- source:
--   D1Bound5/PairClosureIndexedChunks.lean, lines 60-89, SHA-256 29488713ab2248b4e724873977d8278f8e302994a76dfd2d1c47bf8aa3e6e226. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions

section
namespace D1Bound5
open QuadInt








theorem _root_.D1Bound5.pairIndexedWitnessesPrefixBool_add {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (m n : ℕ) (witnesses : List (PairRootWitness tau nu))
    (destinations : List (Option Nat × Option Nat)) :
    pairIndexedWitnessesPrefixBool a b r0 bound vertices (m + n) witnesses destinations =
      (pairIndexedWitnessesPrefixBool a b r0 bound vertices m witnesses destinations &&
        pairIndexedWitnessesPrefixBool a b r0 bound vertices n
          (witnesses.drop m) (destinations.drop m)) := by sorry



end D1Bound5
end
