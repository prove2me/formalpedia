-- Prove2me | Theorems.Thm_D1Bound5_finiteFixedHomogeneous_neg
-- name    : D1Bound5.finiteFixedHomogeneous_neg
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:40.679756+00:00
-- url     : https://prove2.me/theorems/713b2e2f-d817-4324-b82b-0d652e729753
-- title:
--   Finite Fixed Homogeneous neg
-- statement:
--   Simultaneous negation changes a homogeneous polynomial only by its degree sign, so the evaluated coefficient norm is preserved.
-- source:
--   D1Bound5/FiniteFixedCoefficientNorm.lean, lines 13-28, SHA-256 0377e13b3a9896f56e322f66c770742b1eb5de361004a2ea101e2fe972d29e82. Project: https://github.com/tomislav-math/d1-bound5-lean

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
namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.finiteFixedHomogeneous_neg {R : Type*} [CommRing R]
    (n : ℕ) (v : Fin (n+1) → ℤ) (x y : R) :
    finiteHomogeneousTwo n v (-x) (-y) = (-1)^n*finiteHomogeneousTwo n v x y := by sorry




end D1Bound5
end
