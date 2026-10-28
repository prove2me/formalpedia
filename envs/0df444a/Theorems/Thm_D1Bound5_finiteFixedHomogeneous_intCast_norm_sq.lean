-- Prove2me | Theorems.Thm_D1Bound5_finiteFixedHomogeneous_intCast_norm_sq
-- name    : D1Bound5.finiteFixedHomogeneous_intCast_norm_sq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:26.301892+00:00
-- url     : https://prove2.me/theorems/c4553591-956c-491b-b8a9-6a0b81e24c96
-- title:
--   Finite Fixed Homogeneous int Cast norm sq
-- statement:
--   Integer-anchor evaluation has the same squared complex modulus as its quadratic-algebra norm in every coordinate model. No identification of the ambient number field with the Gaussian field is required.
-- source:
--   D1Bound5/FiniteRationalCoefficientNorm.lean, lines 8-26, SHA-256 cbb8acb5119cfcd9b5595fbd26ec802e6aa6c61c6692316b5eef8bf917230de6. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.finiteFixedHomogeneous_intCast_norm_sq (tau nu : ℤ)
    (n : ℕ) (v : Fin (n+1) → ℤ) (X Y : ℤ) :
    ‖finiteHomogeneousTwo n v (X : ℂ) (Y : ℂ)‖^2 =
      ((finiteHomogeneousTwo n v (X : QuadInt tau nu) (Y : QuadInt tau nu)).norm : ℝ) := by sorry





end D1Bound5
end
