-- Prove2me | Theorems.Thm_D1Bound5_mixedFour_operator_norm_le
-- name    : D1Bound5.mixedFour_operator_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:04.132562+00:00
-- url     : https://prove2.me/theorems/3e8adee7-19a9-4db7-9b97-3bf428ae58c9
-- title:
--   Mixed Four operator norm le
-- statement:
--   The concrete mixed 4x4 weighted Schur operator-norm estimate needed in the A >= 1, B >= 3 branch of manuscript Lemma product-four.
-- source:
--   D1Bound5/WeightedSchur.lean, lines 144-157, SHA-256 0740899bda0b97ce5440dc1a326c7e0aa61aa178424db90f7d296c6acdfafdf8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
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



end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5




theorem _root_.D1Bound5.mixedFour_operator_norm_le
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hdiag : ∀ i, E i i = 0)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖E i j‖ < (1 / 18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖E i j‖ < (1 / 64 : ℝ)) :
    ‖E‖ ≤ (11 / 96 : ℝ) := by sorry

end D1Bound5
end
