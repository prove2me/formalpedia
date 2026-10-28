-- Prove2me | Theorems.Thm_D1Bound5_crossBlock_rootMatrix_det_ne_zero
-- name    : D1Bound5.crossBlock_rootMatrix_det_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:23.304265+00:00
-- url     : https://prove2.me/theorems/5d01d36f-43e6-486a-b78c-ee950d54eda3
-- title:
--   Cross Block root Matrix det ne zero
-- statement:
--   The algebraic nonvanishing assertion in the cross-block lemma. A three-by-three matrix of arbitrarily signed square roots of `a i*b j+1` has nonzero determinant whenever the three row parameters and three column parameters are separately distinct. No nonzero-coordinate or nonzero-root hypothesis is needed. The proof works in every characteristic-zero integral domain, in particular in the full ring of integers of a number field.
-- source:
--   D1Bound5/CrossBlockDeterminant.lean, lines 122-159, SHA-256 cd6114eda30e1efcab5d9caabda7a9fe3c6ed338040456745dfdf25b3b2550b3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5








theorem _root_.D1Bound5.crossBlock_rootMatrix_det_ne_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (a b : Fin 3 → K) (R : Matrix (Fin 3) (Fin 3) K)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hroot : ∀ i j, (R i j)^2 = a i*b j+1) :
    R.det ≠ 0 := by sorry



end D1Bound5
end
