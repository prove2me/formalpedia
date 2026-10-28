-- Prove2me | Theorems.Thm_D1Bound5_first_pair_root_norm_le_eight
-- name    : D1Bound5.first_pair_root_norm_le_eight
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:20:38.060593+00:00
-- url     : https://prove2.me/theorems/43cef7b9-933a-443f-be85-7494fbd00826
-- title:
--   First pair root norm le eight
-- statement:
--   A root of a first-pair product needs only the norm-eight disk.
-- source:
--   D1Bound5/OneSmallFiniteCheck.lean, lines 7-33, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.first_pair_root_norm_le_eight {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b q : QuadInt tau nu)
    (hab : a.norm*b.norm ≤ 63) (hq : q*q = a*b+1) : q.norm ≤ 8 := by sorry





















end D1Bound5
end
