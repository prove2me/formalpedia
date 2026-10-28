-- Prove2me | Theorems.Thm_D1Bound5_small_tail_parameter_range
-- name    : D1Bound5.small_tail_parameter_range
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:21:00.906696+00:00
-- url     : https://prove2.me/theorems/a1523ed9-3407-4972-9d96-3bffeaee8fcf
-- title:
--   Small tail parameter range
-- statement:
--   In the normalized full integral basis, a positive discriminant at most 60 forces the remaining generator coefficient to lie between 1 and 15. This stronger uniform rectangular reduction deliberately includes all 30 trace/parameter pairs, even models not needed for maximal orders.
-- source:
--   D1Bound5/SmallTailRange.lean, lines 6-21, SHA-256 c865f417a7e67904d3233f7fda419d37747223d0ad8cd78c1681f681b53a4c0d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.small_tail_parameter_range (tau nu : ℤ)
    (htau : tau = 0 ∨ tau = 1)
    (hpos : 0 < QuadInt.discriminant tau nu)
    (hcut : QuadInt.discriminant tau nu ≤ 60) :
    1 ≤ nu ∧ nu ≤ 15 := by sorry



end D1Bound5
end
