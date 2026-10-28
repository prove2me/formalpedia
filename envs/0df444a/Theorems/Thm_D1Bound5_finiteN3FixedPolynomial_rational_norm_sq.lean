-- Prove2me | Theorems.Thm_D1Bound5_finiteN3FixedPolynomial_rational_norm_sq
-- name    : D1Bound5.finiteN3FixedPolynomial_rational_norm_sq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:22:32.675879+00:00
-- url     : https://prove2.me/theorems/a162cd01-c432-4507-9065-22d34b5a03eb
-- title:
--   Finite N3Fixed Polynomial rational norm sq
-- statement:
--   Signed integer anchors have the certified coefficient norms in every number field. Conjugation fixes the integer anchors automatically.
-- source:
--   D1Bound5/FiniteN3RationalHeight.lean, lines 66-79, SHA-256 5a89bed06adf0092d8b8d7a042ed680435a9f3c4505cc6ce344dc83a77198e63. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteN3FixedHeight_Definitions

section
open scoped NumberField

namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.finiteN3FixedPolynomial_rational_norm_sq
    {K : Type*} [Field K] [NumberField K] (phi : K →+* ℂ)
    (tau nu : ℤ) (X Y : ℤ) (sgn : Bool) (x y : 𝓞 K)
    (hx : x = if sgn then -(X : 𝓞 K) else (X : 𝓞 K))
    (hy : y = if sgn then -(Y : 𝓞 K) else (Y : 𝓞 K))
    (i : Fin 3) (j : Fin 2) (ell : Fin 4) :
    ‖finiteN3FixedPolynomial (phi (x : K)) (phi (y : K)) i j ell‖^2 =
      ((finiteN3FixedPolynomial (X : QuadInt tau nu) (Y : QuadInt tau nu) i j ell).norm : ℝ) := by sorry

end D1Bound5
end
