-- Prove2me | Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_no_three_nonzero
-- name    : D1Bound5.pairGraphTriangleFreeBool_of_no_three_nonzero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:14.630106+00:00
-- url     : https://prove2.me/theorems/a25e7d33-3fb9-40dc-b58a-5fe4b6387cdf
-- title:
--   Pair Graph Triangle Free Bool of no three nonzero
-- statement:
--   A mathematical exclusion of three nonzero compatible points supplies exactly the original triangle Boolean, without enumerating the pairs.
-- source:
--   D1Bound5/PairGraphNoThreeTransfer.lean, lines 6-45, SHA-256 10b2bdca2160b3f93442ff75882d77cb4a22b0c8e74c0b3b0b8565bc741f9adb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions

section
namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.pairGraphTriangleFreeBool_of_no_three_nonzero {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (hvalid : CoordinateSquareSieveValid tau nu sieve)
    (vertices : List (QuadInt tau nu))
    (hno : ∀ x y z : QuadInt tau nu,
      x ∈ vertices → y ∈ vertices → z ∈ vertices →
      x ≠ 0 → y ≠ 0 → z ≠ 0 →
      (∃ r, r*r = x*y+1) → (∃ r, r*r = x*z+1) →
      (∃ r, r*r = y*z+1) → False) :
    pairGraphTriangleFreeBool sieve vertices = true := by sorry





end D1Bound5
end
