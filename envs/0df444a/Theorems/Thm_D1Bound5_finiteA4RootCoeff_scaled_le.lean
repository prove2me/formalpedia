-- Prove2me | Theorems.Thm_D1Bound5_finiteA4RootCoeff_scaled_le
-- name    : D1Bound5.finiteA4RootCoeff_scaled_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:14:27.399666+00:00
-- url     : https://prove2.me/theorems/3283affc-3363-427f-897b-f43b37e3d1ca
-- title:
--   Finite A4Root Coeff scaled le
-- statement:
--   Auxiliary result `finiteA4RootCoeff_scaled_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA4FixedHeight.lean, lines 70-90, SHA-256 9da23d107d5468a905083d70a610cff62cd23f973ea59fa3341b16e9257eb2fb. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt











theorem _root_.D1Bound5.finiteA4RootCoeff_scaled_le
    (B C W X : ℝ) (ell : Fin 5) (hB : 0 < B) (hC : 1000 ≤ C)
    (hCB : 200*B ≤ C) (hW : 0 ≤ W) (hX : 0 ≤ X)
    (hsq : X^2 ≤ if B^2 ≤ 25 then W^2*(B^2)^9*1000^(8-2*(ell : ℕ))
      else W^2*(B^2)^(13-(ell : ℕ))*200^(8-2*(ell : ℕ))) :
    X*C^(ell : ℕ) ≤ W*B^9*C^4 := by sorry



end D1Bound5
end
