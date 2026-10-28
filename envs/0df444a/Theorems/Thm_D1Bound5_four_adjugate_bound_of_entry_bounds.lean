-- Prove2me | Theorems.Thm_D1Bound5_four_adjugate_bound_of_entry_bounds
-- name    : D1Bound5.four_adjugate_bound_of_entry_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:21:15.564796+00:00
-- url     : https://prove2.me/theorems/9d07dcea-3df1-4b2f-be29-67e429d55ee5
-- title:
--   Four adjugate bound of entry bounds
-- statement:
--   Once the diagonal/off-diagonal cofactor errors have their explicit cubic estimates, the required L2 adjugate bound follows. This statement exposes the two scalar inequalities as hypotheses.
-- source:
--   D1Bound5/AdjugateFourBounds.lean, lines 76-106, SHA-256 e5781cd0cc609ab6e464413c644de534702a0bca3e48c68b9e060b00a6b88c13. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
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
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







end D1Bound5


namespace D1Bound5




theorem _root_.D1Bound5.four_adjugate_bound_of_entry_bounds
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, ‖(F.adjugate - halfOffDiagonal.adjugate) i i‖ <
      (23/1000 : ℝ))
    (hoff : ∀ i j, i ≠ j →
      ‖(F.adjugate - halfOffDiagonal.adjugate) i j‖ <
        (197/10000 : ℝ)) :
    ‖F.adjugate‖ < productFourH * productFourS^2 := by sorry

end D1Bound5

namespace D1Bound5



end D1Bound5
end
