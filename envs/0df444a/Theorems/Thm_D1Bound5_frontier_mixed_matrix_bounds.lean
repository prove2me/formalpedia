-- Prove2me | Theorems.Thm_D1Bound5_frontier_mixed_matrix_bounds
-- name    : D1Bound5.frontier_mixed_matrix_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:26.400175+00:00
-- url     : https://prove2.me/theorems/2453f4aa-6e4e-4bf6-9c7a-f3a45929349d
-- title:
--   Frontier mixed matrix bounds
-- statement:
--   The mixed six-variable cofactor bounds apply to any symmetric zero-diagonal matrix with the designated first-row error envelope.
-- source:
--   D1Bound5/FrontierMixedDeterminant.lean, lines 9-40, SHA-256 8971d5daa3b2a953daf0d876b723a6ea463e6a13433a1770a4414d8aa48c3133. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5


theorem _root_.D1Bound5.frontier_mixed_matrix_bounds (F : Matrix (Fin 4) (Fin 4) ℂ) (k l : ℝ)
    (hl : (1/2 : ℝ) ≤ l) (hlk : l ≤ k)
    (hd : ∀ i, F i i = 0) (hs : ∀ i j, F i j = F j i)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j-(1/2 : ℂ)‖ ≤ k-1/2)
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j-(1/2 : ℂ)‖ ≤ l-1/2) :
    ‖F.det‖ ≤ 9*k^2*l^2 ∧
    ∀ i j, ‖F.adjugate i j‖ ≤ if i = j then 2*(k^2*l) else 3*(k^2*l)-1/4 := by sorry



end D1Bound5
end
