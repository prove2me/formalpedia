-- Prove2me | Theorems.Thm_D1Bound5_five_schur_det_ne_zero_of_near
-- name    : D1Bound5.five_schur_det_ne_zero_of_near
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:19.278618+00:00
-- url     : https://prove2.me/theorems/6974c067-a704-49d6-b79b-54ca076074f3
-- title:
--   Five schur det ne zero of near
-- statement:
--   A one-half operator-norm neighborhood of the reference matrix is nonsingular. This supplies the needed nonvanishing in product-five.
-- source:
--   D1Bound5/ProductFiveArithmeticClosure.lean, lines 38-52, SHA-256 0da19bb1f7a607bd1cb647f269c6c5f92cae2602755ad9eddbe0deb76e5a496d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped NumberField BigOperators Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5






theorem _root_.D1Bound5.five_schur_det_ne_zero_of_near
    (G : Matrix (Fin 4) (Fin 4) ℂ)
    (hnear : ‖G - halfOffDiagonal‖ < (1/2 : ℝ)) :
    G.det ≠ 0 := by sorry





end D1Bound5
end
