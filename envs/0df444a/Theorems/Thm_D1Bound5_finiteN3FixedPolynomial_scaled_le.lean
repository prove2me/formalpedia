-- Prove2me | Theorems.Thm_D1Bound5_finiteN3FixedPolynomial_scaled_le
-- name    : D1Bound5.finiteN3FixedPolynomial_scaled_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:18:51.107509+00:00
-- url     : https://prove2.me/theorems/736e9af4-f539-4437-a5b5-b9a4749aeae4
-- title:
--   Finite N3Fixed Polynomial scaled le
-- statement:
--   Auxiliary result `finiteN3FixedPolynomial_scaled_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteN3FixedHeight.lean, lines 87-107, SHA-256 0b044a9920f89d86943094e723cbd783c3c11f89d494288bfcbb6b25925d3410. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt
















theorem _root_.D1Bound5.finiteN3FixedPolynomial_scaled_le
    (B C W X : ℝ) (ell : Fin 4) (hB : 0 < B) (hC : 1000 ≤ C)
    (hCB : 200*B ≤ C) (hW : 0 ≤ W) (hX : 0 ≤ X)
    (hsq : X^2 ≤ if B^2 ≤ 25 then W^2*(B^2)^7*1000^(6-2*(ell : ℕ))
      else W^2*(B^2)^(10-(ell : ℕ))*200^(6-2*(ell : ℕ))) :
    X*C^(ell : ℕ) ≤ W*B^7*C^3 := by sorry



end D1Bound5
end
