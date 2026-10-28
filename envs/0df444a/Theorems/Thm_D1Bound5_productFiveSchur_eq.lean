-- Prove2me | Theorems.Thm_D1Bound5_productFiveSchur_eq
-- name    : D1Bound5.productFiveSchur_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:46.870007+00:00
-- url     : https://prove2.me/theorems/2d895f05-e26b-47e2-9880-5f07a725a5e8
-- title:
--   Product Five Schur eq
-- statement:
--   The Schur complement is exactly the rank-two perturbation.
-- source:
--   D1Bound5/ProductFiveRankTwo.lean, lines 170-182, SHA-256 0cec92c96e51a0a3fbd94ad6a62d3e917e83332e75de37d2fd74599e197b4902. Project: https://github.com/tomislav-math/d1-bound5-lean

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






















theorem _root_.D1Bound5.productFiveSchur_eq
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ) :
    productFiveSchur F f w d =
      F + productFiveColumns f w * productFiveRows f w d := by sorry



end D1Bound5
end
