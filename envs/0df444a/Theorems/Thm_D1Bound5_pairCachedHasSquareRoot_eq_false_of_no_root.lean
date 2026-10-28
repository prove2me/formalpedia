-- Prove2me | Theorems.Thm_D1Bound5_pairCachedHasSquareRoot_eq_false_of_no_root
-- name    : D1Bound5.pairCachedHasSquareRoot_eq_false_of_no_root
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:53.275476+00:00
-- url     : https://prove2.me/theorems/fc9b74a8-e26c-429b-b4dd-52429b0f0e76
-- title:
--   Pair Cached Has Square Root eq false of no root
-- statement:
--   An actual nonsquare makes the existing exact cached pair test false, regardless of the supplied modular signatures.
-- source:
--   D1Bound5/PairCachedFloorWitnesses.lean, lines 7-18, SHA-256 344ed1b90b84f82b59da3776e3d6e5f30a12a3e268e2e655e2aac504ca085b06. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.pairCachedHasSquareRoot_eq_false_of_no_root {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (x y : PairResidueVertex tau nu)
    (hnot : ¬ ∃ r : QuadInt tau nu, r * r = x.vertex * y.vertex + 1) :
    pairCachedHasSquareRoot sieve x y = false := by sorry















end D1Bound5
end
