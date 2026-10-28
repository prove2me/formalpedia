-- Prove2me | Theorems.Thm_D1Bound5_productFive_scalar_det_upper
-- name    : D1Bound5.productFive_scalar_det_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:34:25.411983+00:00
-- url     : https://prove2.me/theorems/bb893f20-c8eb-4c96-927e-1b2a01f95988
-- title:
--   Product Five scalar det upper
-- statement:
--   The exact rational determinant margin in the five-entry Schur argument. All four bilinear quantities are complex, with no Hermitian assumptions.
-- source:
--   D1Bound5/ProductFiveDetNumeric.lean, lines 8-66, SHA-256 8332341e11d4117d48af2f4f0ac1c61b87c0fa8ae2cf858eab23c5eb17b658fa. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.productFive_scalar_det_upper
    (a h p q d : ℂ) (hd : d ≠ 0)
    (ha : ‖a‖ ≤ (33/128 : ℝ))
    (hh : ‖h/d‖ ≤ (11/108 : ℝ))
    (hp : ‖p‖ ≤ (1 : ℝ))
    (hq : ‖q/d^2‖ ≤ (8/243 : ℝ))
    (hpd : ‖p/d^2‖ ≤ (1/2916 : ℝ)) :
    ‖a * (1 - 2*h/d + (h^2 - p*q - p)/d^2)‖ < (1/3 : ℝ) := by sorry



end D1Bound5
end
