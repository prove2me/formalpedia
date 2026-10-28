-- Prove2me | Theorems.Thm_D1Bound5_productFour_ordered_square_sum
-- name    : D1Bound5.productFour_ordered_square_sum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:57.268678+00:00
-- url     : https://prove2.me/theorems/66e9f091-d4cc-487a-9fb0-0fa7e99b81e8
-- title:
--   Product Four ordered square sum
-- statement:
--   A quantitative square-sum estimate from the already established irregular-growth inequality. The entries may have equal moduli.
-- source:
--   D1Bound5/ProductFourLargeBranch.lean, lines 11-32, SHA-256 4851402ecfc8290d9255d8a258c4878b20354f6555e88cd106cf24ffdca061f8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
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

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5


theorem _root_.D1Bound5.productFour_ordered_square_sum
    (A B C D : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B)
    (hBC : B ≤ C) (hB : 3 ≤ B) (htail : 2*B*C < D) :
    A^2+B^2+C^2+D^2 ≤ (13/12 : ℝ)*D^2 := by sorry



end D1Bound5

namespace D1Bound5



end D1Bound5
end
