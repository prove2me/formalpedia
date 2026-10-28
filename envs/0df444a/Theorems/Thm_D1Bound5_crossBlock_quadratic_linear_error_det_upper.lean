-- Prove2me | Theorems.Thm_D1Bound5_crossBlock_quadratic_linear_error_det_upper
-- name    : D1Bound5.crossBlock_quadratic_linear_error_det_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:35.134993+00:00
-- url     : https://prove2.me/theorems/a3831ca0-b3eb-4ab1-8a07-ceb4fa572f77
-- title:
--   Cross Block quadratic linear error det upper
-- statement:
--   A finite determinant estimate for two rank-one layers plus a uniformly bounded error matrix. No power series or limiting Cauchy--Binet identity is needed. The pair hypothesis records distinct rows and columns.
-- source:
--   D1Bound5/CrossBlockUpper.lean, lines 101-137, SHA-256 751cfc90c8157cd148f1ea291c9c2514ef722d3e7ded4f856850dac4856d5706. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5








theorem _root_.D1Bound5.crossBlock_quadratic_linear_error_det_upper
    (a b : Fin 3 → ℂ) (E : Fin 3 → Fin 3 → ℂ)
    (M P c : ℝ) (hM : 0 ≤ M) (hP : 0 ≤ P) (hc : 0 ≤ c)
    (hentry : ∀ i j, ‖a i*b j‖ ≤ M)
    (hpair : ∀ i j k l, i ≠ j → k ≠ l →
      ‖(a i*b k)^2*(a j*b l)‖ ≤ P)
    (hE : ∀ i j, ‖E i j‖ ≤ c) :
    ‖Matrix.det (Matrix.of (fun i j => (a i*b j)^2+(1/2 : ℂ)*(a i*b j)+E i j))‖ ≤
      18*P*c+18*M^2*c^2+9*M*c^2+6*c^3 := by sorry

end D1Bound5
end
