-- Prove2me | Theorems.Thm_D1Bound5_symmetric_inverse_bilinear_swap
-- name    : D1Bound5.symmetric_inverse_bilinear_swap
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:36.268535+00:00
-- url     : https://prove2.me/theorems/b0261313-e7e1-4edc-a50a-552845950b81
-- title:
--   Symmetric inverse bilinear swap
-- statement:
--   Symmetry of the complex bilinear form of the inverse. No complex conjugation occurs; this is the ordinary transpose.
-- source:
--   D1Bound5/ProductFiveRankTwo.lean, lines 133-142, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902. Project: https://github.com/tomislav-math/d1-bound5-lean

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
















theorem _root_.D1Bound5.symmetric_inverse_bilinear_swap
    (F : Matrix (Fin 4) (Fin 4) ℂ) (f w : Fin 4 → ℂ)
    (hsym : Fᵀ = F) :
    w ⬝ᵥ (F⁻¹ *ᵥ f) = f ⬝ᵥ (F⁻¹ *ᵥ w) := by sorry









end D1Bound5
end
