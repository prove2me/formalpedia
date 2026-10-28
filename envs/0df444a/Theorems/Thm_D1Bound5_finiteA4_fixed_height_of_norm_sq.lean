-- Prove2me | Theorems.Thm_D1Bound5_finiteA4_fixed_height_of_norm_sq
-- name    : D1Bound5.finiteA4_fixed_height_of_norm_sq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:04:35.633731+00:00
-- url     : https://prove2.me/theorems/25028aee-667d-42f6-84d7-9deaf0187670
-- title:
--   Finite A4 fixed height of norm sq
-- statement:
--   Exact coefficient norm identities suffice for height transfer; no identification of the ambient field with a coordinate ring is needed.
-- source:
--   D1Bound5/FiniteA4RationalHeight.lean, lines 9-64, SHA-256 89101dc5175b482e62535a694b28dc934e907cada3f4e3049e95139b18084dbb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA4FixedHeight_Definitions
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions

section
open scoped NumberField

namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.finiteA4_fixed_height_of_norm_sq {tau nu : ℤ}
    (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 5 → ℚ) (hbound : FiniteA4FixedBound a b M w)
    (X Y Z : ℂ) (hBsq : ‖Y‖^2 = (b.norm : ℝ))
    (hnorm : ∀ i j ell, ‖finiteA4RootCoeff X Y i j ell‖^2 =
      ((finiteA4RootCoeff a b i j ell).norm : ℝ))
    (hy0 : Y ≠ 0) (hC : 1000 ≤ ‖Z‖) (hCB : 200*‖Y‖ ≤ ‖Z‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA4Left X Y Z i‖+‖finiteA4Right X Y Z i‖) <
      (M : ℝ)*‖Y‖^9*‖Z‖^4 := by sorry



end D1Bound5
end
