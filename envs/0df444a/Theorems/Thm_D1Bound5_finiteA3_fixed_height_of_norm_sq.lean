-- Prove2me | Theorems.Thm_D1Bound5_finiteA3_fixed_height_of_norm_sq
-- name    : D1Bound5.finiteA3_fixed_height_of_norm_sq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:57:46.507807+00:00
-- url     : https://prove2.me/theorems/b6a5d93d-d5a8-4c6c-9b2a-7ed91aced447
-- title:
--   Finite A3 fixed height of norm sq
-- statement:
--   Exact coefficient norm identities suffice for height transfer; no identification of the ambient field with a coordinate ring is needed.
-- source:
--   D1Bound5/FiniteA3RationalHeight.lean, lines 9-64, SHA-256 33fa762b748cfb2f558b74529d3b8fad1baf527d7d00b80735c918244387522d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA3FixedHeight_Definitions
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions

section
open scoped NumberField

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.finiteA3_fixed_height_of_norm_sq {tau nu : ℤ}
    (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 4 → ℚ) (hbound : FiniteA3FixedBound a b M w)
    (X Y Z : ℂ) (hBsq : ‖Y‖^2 = (b.norm : ℝ))
    (hnorm : ∀ i j ell, ‖finiteA3RootCoeff X Y i j ell‖^2 =
      ((finiteA3RootCoeff a b i j ell).norm : ℝ))
    (hy0 : Y ≠ 0) (hC : 1000 ≤ ‖Z‖) (hCB : 200*‖Y‖ ≤ ‖Z‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA3Left X Y Z i‖+‖finiteA3Right X Y Z i‖) <
      (M : ℝ)*‖Y‖^6*‖Z‖^3 := by sorry



end D1Bound5
end
