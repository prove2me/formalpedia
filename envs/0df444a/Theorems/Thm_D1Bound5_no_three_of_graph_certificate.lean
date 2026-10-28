-- Prove2me | Theorems.Thm_D1Bound5_no_three_of_graph_certificate
-- name    : D1Bound5.no_three_of_graph_certificate
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:36:44.831418+00:00
-- url     : https://prove2.me/theorems/851988ff-de18-4582-a040-8084fd5605f1
-- title:
--   No three of graph certificate
-- statement:
--   The finite graph certificate rules out three compatible vertices with arbitrary coordinate size. There is no unverified graph computation.
-- source:
--   D1Bound5/SmallPairGraphCheck.lean, lines 33-58, SHA-256 a1fd39ac1e63a1a407d5fbedb3ad3d7599b1489a8857fc7d2c2d3c2c9b4396e6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.no_three_of_graph_certificate {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (hvalid : CoordinateSquareSieveValid tau nu sieve) (vertices : List (QuadInt tau nu))
    (hcheck : pairGraphTriangleFreeBool sieve vertices = true)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hmem : ∀ i, t i ∈ vertices) : False := by sorry



end D1Bound5
end
