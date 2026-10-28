-- Prove2me | Theorems.Thm_D1Bound5_mixed_zero_four_det_norm_lt
-- name    : D1Bound5.mixed_zero_four_det_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:32.223481+00:00
-- url     : https://prove2.me/theorems/f8729e15-ef5b-4b4f-8883-845a03d49af7
-- title:
--   Mixed zero four det norm lt
-- statement:
--   The mixed determinant bound in a matrix-independent index interface.
-- source:
--   D1Bound5/MixedFourDetBound.lean, lines 138-164, SHA-256 863a07b764253ce476290edc497efddecf3c39545921323e93756d8912d3da78. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open Matrix

namespace D1Bound5







end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.mixed_zero_four_det_norm_lt
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, F i i = 0)
    (hsymm : ∀ i j, F i j = F j i)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j - (1/2 : ℂ)‖ < (1/18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j - (1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖F.det‖ < (3/10 : ℝ) := by sorry

end D1Bound5

namespace D1Bound5



end D1Bound5
end
