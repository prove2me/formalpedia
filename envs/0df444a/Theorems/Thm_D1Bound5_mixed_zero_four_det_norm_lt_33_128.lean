-- Prove2me | Theorems.Thm_D1Bound5_mixed_zero_four_det_norm_lt_33_128
-- name    : D1Bound5.mixed_zero_four_det_norm_lt_33_128
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:22:18.929786+00:00
-- url     : https://prove2.me/theorems/5d95bac9-65b7-460a-9959-3b6281863f00
-- title:
--   Mixed zero four det norm lt 33 128
-- statement:
--   Matrix-index version, with no invertibility or root-nonzero hypothesis.
-- source:
--   D1Bound5/ProductFivePrefixDet.lean, lines 122-148, SHA-256 f9937f549ad5792258cef7e7ac08638bae75b2a7351c4bdd51aa581d8bdd481f. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.mixed_zero_four_det_norm_lt_33_128
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, F i i = 0)
    (hsymm : ∀ i j, F i j = F j i)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j - (1/2 : ℂ)‖ < (1/18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j - (1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖F.det‖ < (33/128 : ℝ) := by sorry

end D1Bound5
end
