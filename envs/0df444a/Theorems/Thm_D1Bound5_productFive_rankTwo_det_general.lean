-- Prove2me | Theorems.Thm_D1Bound5_productFive_rankTwo_det_general
-- name    : D1Bound5.productFive_rankTwo_det_general
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:36:59.297894+00:00
-- url     : https://prove2.me/theorems/a7037fbc-2a49-4667-a07e-e30bfa15314a
-- title:
--   Product Five rank Two det general
-- statement:
--   The exact rank-two determinant formula for the fifth-entry Schur complement. No symmetry is assumed: both cross forms occur. In the symmetric case the two cross forms coincide.
-- source:
--   D1Bound5/ProductFiveRankTwo.lean, lines 87-131, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902. Project: https://github.com/tomislav-math/d1-bound5-lean

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














theorem _root_.D1Bound5.productFive_rankTwo_det_general
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ)
    (hF : F.det ≠ 0) (hd : d ≠ 0) :
    (F + productFiveColumns f w * productFiveRows f w d).det =
      F.det *
        (1 - ((w ⬝ᵥ (F⁻¹ *ᵥ f)) + (f ⬝ᵥ (F⁻¹ *ᵥ w))) / d +
          ((w ⬝ᵥ (F⁻¹ *ᵥ f)) * (f ⬝ᵥ (F⁻¹ *ᵥ w)) -
            (f ⬝ᵥ (F⁻¹ *ᵥ f)) * (w ⬝ᵥ (F⁻¹ *ᵥ w)) -
            (f ⬝ᵥ (F⁻¹ *ᵥ f))) / d^2) := by sorry











end D1Bound5
end
