-- Prove2me | Theorems.Thm_D1Bound5_mixedSymmetricFour_det_lt_33_128
-- name    : D1Bound5.mixedSymmetricFour_det_lt_33_128
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:35.533445+00:00
-- url     : https://prove2.me/theorems/404859be-6af7-44d6-be2d-f2d081c30636
-- title:
--   Mixed Symmetric Four det lt 33 128
-- statement:
--   Sharpened mixed determinant bound for the exact symmetric matrix.
-- source:
--   D1Bound5/ProductFivePrefixDet.lean, lines 106-120, SHA-256 f9937f549ad5792258cef7e7ac08638bae75b2a7351c4bdd51aa581d8bdd481f. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.mixedSymmetricFour_det_lt_33_128 (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
      Matrix (Fin 4) (Fin 4) ℂ).det‖ < (33/128 : ℝ) := by sorry



end D1Bound5
end
