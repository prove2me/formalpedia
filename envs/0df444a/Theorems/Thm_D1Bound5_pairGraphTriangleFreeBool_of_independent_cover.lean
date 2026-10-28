-- Prove2me | Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_independent_cover
-- name    : D1Bound5.pairGraphTriangleFreeBool_of_independent_cover
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:52.188847+00:00
-- url     : https://prove2.me/theorems/f0410cef-6167-49b6-8ed0-830d3c1d9df1
-- title:
--   Pair Graph Triangle Free Bool of independent cover
-- statement:
--   A certified two-color overgraph supplies the original triangle Boolean. Only within-color nonedges are checked; cross-color pairs remain arbitrary.
-- source:
--   D1Bound5/PairBipartiteCheck.lean, lines 59-116, SHA-256 d1497b46c9dcbae577d7172e6c4401388a1797e68d33ba795d4e6a6a05dd4c0c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions

section
namespace D1Bound5
open QuadInt










theorem _root_.D1Bound5.pairGraphTriangleFreeBool_of_independent_cover {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices left right : List (QuadInt tau nu))
    (hcover : ∀ z ∈ vertices, z ∈ left ∨ z ∈ right)
    (hleft : pairIndependentBool sieve left = true)
    (hright : pairIndependentBool sieve right = true) :
    pairGraphTriangleFreeBool sieve vertices = true := by sorry



end D1Bound5
end
