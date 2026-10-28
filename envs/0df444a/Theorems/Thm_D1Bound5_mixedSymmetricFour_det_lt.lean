-- Prove2me | Theorems.Thm_D1Bound5_mixedSymmetricFour_det_lt
-- name    : D1Bound5.mixedSymmetricFour_det_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:51.062294+00:00
-- url     : https://prove2.me/theorems/15abb19c-431f-46b8-b8da-0fcfdf2b48ce
-- title:
--   Mixed Symmetric Four det lt
-- statement:
--   A symmetric mixed normalized matrix satisfies a uniform determinant bound, with no singular-value or invertibility assumptions.
-- source:
--   D1Bound5/MixedFourDetBound.lean, lines 117-132, SHA-256 863a07b764253ce476290edc497efddecf3c39545921323e93756d8912d3da78. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.mixedSymmetricFour_det_lt (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
      Matrix (Fin 4) (Fin 4) ℂ).det‖ < (3/10 : ℝ) := by sorry

end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5



end D1Bound5
end
