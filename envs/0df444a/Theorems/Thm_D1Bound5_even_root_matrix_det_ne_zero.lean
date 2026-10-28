-- Prove2me | Theorems.Thm_D1Bound5_even_root_matrix_det_ne_zero
-- name    : D1Bound5.even_root_matrix_det_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:30.599761+00:00
-- url     : https://prove2.me/theorems/adcdd096-5b7b-40af-b254-c3f8f9b841c6
-- title:
--   Even root matrix det ne zero
-- statement:
--   The even-dimensional integral root matrix is nonsingular over the full integer ring of every quadratic number field. No quotient properness assumption is added: the explicit reduction has a nontrivial target.
-- source:
--   D1Bound5/EvenDeterminant.lean, lines 80-106, SHA-256 8be5563bc593805dbec0a0a77973231e6167cbe9b0c64e31ce73f3d46b08cc4c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField BigOperators
open Matrix Module

namespace D1Bound5








theorem _root_.D1Bound5.even_root_matrix_det_ne_zero {K n : Type*} [Field K] [NumberField K]
    [Fintype n] [DecidableEq n] (hK : finrank ℚ K = 2)
    (hn : Even (Fintype.card n)) (v : n → 𝓞 K) (M : Matrix n n (𝓞 K))
    (hd : ∀ i, M i i = v i)
    (hs : ∀ i j, i ≠ j → (M i j)^2 = v i*v j+1) : M.det ≠ 0 := by sorry



end D1Bound5
end
