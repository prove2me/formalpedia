-- Prove2me | Theorems.Thm_D1Bound5_symmetricFour_adjugate_norm_lt
-- name    : D1Bound5.symmetricFour_adjugate_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:44.48725+00:00
-- url     : https://prove2.me/theorems/b7f6d4f5-b3ae-4529-8837-ae409096a93d
-- title:
--   Symmetric Four adjugate norm lt
-- statement:
--   Unconditional adjugate operator-norm estimate for all six independently chosen entries satisfying the previously proved near-half bounds.
-- source:
--   D1Bound5/AdjugateCoverage.lean, lines 29-78, SHA-256 f2847afb95c8defcb8c59c5324b1cbe3904cb7236a7d79d7d2486bba6b9076b4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_AdjugateCoverage_Definitions
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5








theorem _root_.D1Bound5.symmetricFour_adjugate_norm_lt (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖(symmetricFour x y z u v w).adjugate‖ <
      productFourH * productFourS^2 := by sorry



end D1Bound5
end
