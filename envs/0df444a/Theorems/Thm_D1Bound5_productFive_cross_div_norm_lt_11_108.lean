-- Prove2me | Theorems.Thm_D1Bound5_productFive_cross_div_norm_lt_11_108
-- name    : D1Bound5.productFive_cross_div_norm_lt_11_108
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:49.982923+00:00
-- url     : https://prove2.me/theorems/785f5942-1b65-4a08-93ca-38065e9ac5c7
-- title:
--   Product Five cross div norm lt 11 108
-- statement:
--   Symmetry turns the cross form into one involving the controlled inverse vector. All norms are Euclidean, while the dot product is complex bilinear.
-- source:
--   D1Bound5/ProductFivePrefixSizeCross.lean, lines 72-97, SHA-256 39ff147d52c592f501114d236d32fbc4150cb62823ddd11060e5fcb20af2215f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix
open scoped NumberField

namespace D1Bound5





end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.productFive_cross_div_norm_lt_11_108
    (F : Matrix (Fin 4) (Fin 4) ℂ) (v w : Fin 4 → ℂ) (d : ℂ)
    (hd : d ≠ 0) (hsym : Fᵀ = F)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ <
      ‖d‖ / 9)
    (hFv : ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) :
      EuclideanSpace ℂ (Fin 4))‖ < (11/12 : ℝ)) :
    ‖(v ⬝ᵥ (F⁻¹ *ᵥ w))/d‖ < (11/108 : ℝ) := by sorry

end D1Bound5
end
