-- Prove2me | Theorems.Thm_D1Bound5_nondegenerate_small_pair_parameter_bound
-- name    : D1Bound5.nondegenerate_small_pair_parameter_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:19.069461+00:00
-- url     : https://prove2.me/theorems/b4c9aed7-d398-4ade-be53-9dcef5ccbf28
-- title:
--   Nondegenerate small pair parameter bound
-- statement:
--   Every nondegenerate compatible small pair belongs to a finite rectangle of normalized coordinate parameters.
-- source:
--   D1Bound5/SmallPairLargeDiscriminant.lean, lines 97-115, SHA-256 c69437fd6732a6665be073a5675405812d333a1b31dbbd565010be6a462d9850. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.nondegenerate_small_pair_parameter_bound {tau nu : ℤ}
    (htau : tau = 0 ∨ tau = 1) (hd : 0 < discriminant tau nu)
    (a b : QuadInt tau nu) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8)
    (hsquare : ∃ r, r*r = a*b+1) (hnondeg : a*b+1 ≠ 0) :
    discriminant tau nu ≤ 32 ∧ 1 ≤ nu ∧ nu ≤ 8 := by sorry

end D1Bound5
end
