-- Prove2me | Theorems.Thm_D1Bound5_productFive_schur_det_upper_of_bilinear_bounds
-- name    : D1Bound5.productFive_schur_det_upper_of_bilinear_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:17.554725+00:00
-- url     : https://prove2.me/theorems/5f63ca88-95e1-4db7-8fd1-360cc7d36980
-- title:
--   Product Five schur det upper of bilinear bounds
-- statement:
--   Apply the scalar margin to the actual rank-two Schur complement. The remaining hypotheses are precisely the normalized analytic estimates.
-- source:
--   D1Bound5/ProductFiveDetNumeric.lean, lines 68-84, SHA-256 8332341e11d4117d48af2f4f0ac1c61b87c0fa8ae2cf858eab23c5eb17b658fa. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.productFive_schur_det_upper_of_bilinear_bounds
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ)
    (hF : F.det ≠ 0) (hd : d ≠ 0)
    (hsym : Fᵀ = F)
    (ha : ‖F.det‖ ≤ (33/128 : ℝ))
    (hh : ‖(f ⬝ᵥ (F⁻¹ *ᵥ w))/d‖ ≤ (11/108 : ℝ))
    (hp : ‖f ⬝ᵥ (F⁻¹ *ᵥ f)‖ ≤ (1 : ℝ))
    (hq : ‖(w ⬝ᵥ (F⁻¹ *ᵥ w))/d^2‖ ≤ (8/243 : ℝ))
    (hpd : ‖(f ⬝ᵥ (F⁻¹ *ᵥ f))/d^2‖ ≤ (1/2916 : ℝ)) :
    ‖(productFiveSchur F f w d).det‖ < (1/3 : ℝ) := by sorry

end D1Bound5
end
