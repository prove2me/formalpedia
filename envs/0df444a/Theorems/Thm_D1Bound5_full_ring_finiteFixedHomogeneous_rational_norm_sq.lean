-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteFixedHomogeneous_rational_norm_sq
-- name    : D1Bound5.full_ring_finiteFixedHomogeneous_rational_norm_sq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:46:25.673605+00:00
-- url     : https://prove2.me/theorems/54cd9aa3-da03-4752-9ada-ba11e6d0b84c
-- title:
--   Full ring finite Fixed Homogeneous rational norm sq
-- statement:
--   Actual full-ring rational anchors transfer the same finite coefficient certificate in arbitrary number fields, including the row (1,3,8).
-- source:
--   D1Bound5/FiniteRationalCoefficientNorm.lean, lines 40-57, SHA-256 cbb8acb5119cfcd9b5595fbd26ec802e6aa6c61c6692316b5eef8bf917230de6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
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
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions

section
open scoped NumberField

namespace D1Bound5






theorem _root_.D1Bound5.full_ring_finiteFixedHomogeneous_rational_norm_sq
    {K : Type*} [Field K] [NumberField K] (phi : K →+* ℂ)
    (tau nu : ℤ) (n : ℕ) (v : Fin (n+1) → ℤ) (X Y : ℤ)
    (sgn : Bool) (x y : 𝓞 K)
    (hx : x = if sgn then -(X : 𝓞 K) else (X : 𝓞 K))
    (hy : y = if sgn then -(Y : 𝓞 K) else (Y : 𝓞 K)) :
    ‖finiteHomogeneousTwo n v (phi (x : K)) (phi (y : K))‖^2 =
      ((finiteHomogeneousTwo n v (X : QuadInt tau nu) (Y : QuadInt tau nu)).norm : ℝ) := by sorry

end D1Bound5
end
