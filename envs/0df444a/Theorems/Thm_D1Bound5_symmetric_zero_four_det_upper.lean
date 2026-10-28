-- Prove2me | Theorems.Thm_D1Bound5_symmetric_zero_four_det_upper
-- name    : D1Bound5.symmetric_zero_four_det_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:32.793421+00:00
-- url     : https://prove2.me/theorems/154e4af2-e64f-4c55-b658-07f8e1eeca9a
-- title:
--   Symmetric zero four det upper
-- statement:
--   The large-entry determinant bound for any symmetric zero-diagonal matrix with the six entrywise deviations established in RootMatrixSigns.
-- source:
--   D1Bound5/SymmetricFourDetBound.lean, lines 154-176, SHA-256 2a8b9f67b260c4208f344e6df6c355fa9cb7ed11896ad19c480cd1c58d7b2c1c. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.symmetric_zero_four_det_upper
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, F i i = 0)
    (hsymm : ∀ i j, F i j = F j i)
    (hsmall : ∀ i j, i ≠ j →
      ‖F i j - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖F.det‖ < productFourH * productFourS^3 := by sorry

end D1Bound5

namespace D1Bound5





end D1Bound5
end
