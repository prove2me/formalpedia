-- Prove2me | Theorems.Thm_D1Bound5_pairSelectedFloorRowBool_sound
-- name    : D1Bound5.pairSelectedFloorRowBool_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:07.593907+00:00
-- url     : https://prove2.me/theorems/3f504339-8515-4d44-b019-919753789fec
-- title:
--   Pair Selected Floor Row Bool sound
-- statement:
--   Every accepted tag rejects the exact cached pair test or checks an actual repeated vertex. Thus all pairs in the entire tail are covered.
-- source:
--   D1Bound5/PairSelectedFloorWitnesses.lean, lines 33-88, SHA-256 5627d261d76c8200c3ce7a8601856a8cef8aa9e7be044b0ebf81c7f060ce8b74. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Ring.Abs
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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions

section
namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.pairSelectedFloorRowBool_sound {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (x : PairResidueVertex tau nu) (ys : List (PairResidueVertex tau nu))
    (code : ℕ) (ks : List ℕ)
    (hcheck : pairSelectedFloorRowBool sieve x ys code ks = true) :
    (ys.all fun y => if decide (x.vertex = y.vertex) then true
      else !(pairCachedHasSquareRoot sieve x y)) = true := by sorry











end D1Bound5
end
