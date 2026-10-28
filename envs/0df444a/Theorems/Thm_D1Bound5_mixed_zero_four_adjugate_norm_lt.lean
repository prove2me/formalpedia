-- Prove2me | Theorems.Thm_D1Bound5_mixed_zero_four_adjugate_norm_lt
-- name    : D1Bound5.mixed_zero_four_adjugate_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:03.766131+00:00
-- url     : https://prove2.me/theorems/0cc6f7f5-546d-4e39-b64c-07edf1e939fd
-- title:
--   Mixed zero four adjugate norm lt
-- statement:
--   Entrywise mixed perturbations for arbitrary symmetric zero-diagonal F.
-- source:
--   D1Bound5/MixedFourAdjugateBound.lean, lines 70-96, SHA-256 6b32cd9d498ea075f626860a30165f6ef389e005d96b2569ca3fea4cf0f5bd76. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5




theorem _root_.D1Bound5.mixed_zero_four_adjugate_norm_lt
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, F i i = 0)
    (hsymm : ∀ i j, F i j = F j i)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j - (1/2 : ℂ)‖ < (1/18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j - (1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖F.adjugate‖ < (155/96 : ℝ) * (59/96)^2 := by sorry

end D1Bound5
end
