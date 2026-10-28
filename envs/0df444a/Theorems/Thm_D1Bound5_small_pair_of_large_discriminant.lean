-- Prove2me | Theorems.Thm_D1Bound5_small_pair_of_large_discriminant
-- name    : D1Bound5.small_pair_of_large_discriminant
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:25:00.864839+00:00
-- url     : https://prove2.me/theorems/a9e0a6a9-ecf8-4178-af0b-936af30b6215
-- title:
--   Small pair of large discriminant
-- statement:
--   For discriminant above 32, the only compatible small pair is {-1,1}. This includes zero roots and makes no maximal-order or squarefree assumption.
-- source:
--   D1Bound5/SmallPairLargeDiscriminant.lean, lines 33-95, SHA-256 c69437fd6732a6665be073a5675405812d333a1b31dbbd565010be6a462d9850. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt








theorem _root_.D1Bound5.small_pair_of_large_discriminant {tau nu : ℤ}
    (hlarge : 32 < discriminant tau nu) (a b : QuadInt tau nu)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8)
    (hsquare : ∃ r, r*r = a*b+1) :
    (a = -1 ∧ b = 1) ∨ (a = 1 ∧ b = -1) := by sorry



end D1Bound5
end
