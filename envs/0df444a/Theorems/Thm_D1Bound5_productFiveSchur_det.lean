-- Prove2me | Theorems.Thm_D1Bound5_productFiveSchur_det
-- name    : D1Bound5.productFiveSchur_det
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:34:31.708714+00:00
-- url     : https://prove2.me/theorems/fec53530-2a4e-4dd8-8160-c05715d7750f
-- title:
--   Product Five Schur det
-- statement:
--   Exact equation (integrated-3)'s determinant identity in the manuscript: the complex bilinear transpose is NOT a conjugate transpose.
-- source:
--   D1Bound5/ProductFiveRankTwo.lean, lines 184-198, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions

section
open Matrix

namespace D1Bound5
























theorem _root_.D1Bound5.productFiveSchur_det
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ)
    (hF : F.det ≠ 0) (hd : d ≠ 0)
    (hsym : Fᵀ = F) :
    (productFiveSchur F f w d).det =
      F.det *
        (1 - 2 * (f ⬝ᵥ (F⁻¹ *ᵥ w)) / d +
          ((f ⬝ᵥ (F⁻¹ *ᵥ w))^2 -
            (f ⬝ᵥ (F⁻¹ *ᵥ f)) * (w ⬝ᵥ (F⁻¹ *ᵥ w)) -
            (f ⬝ᵥ (F⁻¹ *ᵥ f))) / d^2) := by sorry

end D1Bound5
end
