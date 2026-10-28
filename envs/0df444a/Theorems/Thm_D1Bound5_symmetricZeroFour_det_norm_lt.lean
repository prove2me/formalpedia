-- Prove2me | Theorems.Thm_D1Bound5_symmetricZeroFour_det_norm_lt
-- name    : D1Bound5.symmetricZeroFour_det_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:52.628995+00:00
-- url     : https://prove2.me/theorems/8961ee25-738d-4c57-818d-f496e08f2620
-- title:
--   Symmetric Zero Four det norm lt
-- statement:
--   A direct four-by-four determinant bound, without singular values.
-- source:
--   D1Bound5/SymmetricFourDetBound.lean, lines 134-152, SHA-256 2a8b9f67b260c4208f344e6df6c355fa9cb7ed11896ad19c480cd1c58d7b2c1c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions

section
open Matrix

namespace D1Bound5



end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.symmetricZeroFour_det_norm_lt
    (x y z u v w : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hu : ‖u - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hv : ‖v - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hw : ‖w - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
      Matrix (Fin 4) (Fin 4) ℂ).det‖ <
    productFourH * productFourS^3 := by sorry



end D1Bound5

namespace D1Bound5





end D1Bound5
end
