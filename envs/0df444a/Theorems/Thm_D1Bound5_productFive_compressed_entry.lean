-- Prove2me | Theorems.Thm_D1Bound5_productFive_compressed_entry
-- name    : D1Bound5.productFive_compressed_entry
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:37.052289+00:00
-- url     : https://prove2.me/theorems/5cc9a72d-3545-41e6-8638-3b55cf286170
-- title:
--   Product Five compressed entry
-- statement:
--   All four entries of the two-by-two compressed correction. Its two mixed bilinear terms are deliberately kept distinct, so this lemma does not assume that the inverse matrix is symmetric.
-- source:
--   D1Bound5/ProductFiveRankTwo.lean, lines 66-85, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902. Project: https://github.com/tomislav-math/d1-bound5-lean

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












theorem _root_.D1Bound5.productFive_compressed_entry
    (X : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ) (i j : Fin 2) :
    (productFiveRows f w d * X * productFiveColumns f w) i j =
      if i = 0 then
        (if j = 0 then
          -(w ⬝ᵥ (X *ᵥ f)) / d - (f ⬝ᵥ (X *ᵥ f)) / d^2
         else
          -(w ⬝ᵥ (X *ᵥ w)) / d - (f ⬝ᵥ (X *ᵥ w)) / d^2)
      else
        (if j = 0 then
          -(f ⬝ᵥ (X *ᵥ f)) / d
         else
          -(f ⬝ᵥ (X *ᵥ w)) / d) := by sorry













end D1Bound5
end
