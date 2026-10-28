-- Prove2me | Theorems.Thm_D1Bound5_frontier_large_adjugate_entry_bounds
-- name    : D1Bound5.frontier_large_adjugate_entry_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:47.09769+00:00
-- url     : https://prove2.me/theorems/326451ff-4381-462e-a579-b9da1578710b
-- title:
--   Frontier large adjugate entry bounds
-- statement:
--   Keep diagonal and off-diagonal cofactor bounds separately. This is sharper for the already very unequal tuple coordinates than replacing the adjugate by its operator norm. All estimates are proved dependencies.
-- source:
--   D1Bound5/FrontierLargeCofactors.lean, lines 41-97, SHA-256 b15ff130f21e4ba2c5a497adcd440be4b87140604e8d066a1d6928f84d85a8bd. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5








theorem _root_.D1Bound5.frontier_large_adjugate_entry_bounds
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hzero : ∀ i, F i i = 0) (hsym : ∀ i j, F i j = F j i)
    (hnear : ∀ i j, i ≠ j → ‖F i j-(1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ∀ i j, ‖F.adjugate i j‖ ≤
      if i = j then (273/1000 : ℝ) else (1447/10000 : ℝ) := by sorry

end D1Bound5
end
