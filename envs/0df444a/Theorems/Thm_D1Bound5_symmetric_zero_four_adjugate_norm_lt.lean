-- Prove2me | Theorems.Thm_D1Bound5_symmetric_zero_four_adjugate_norm_lt
-- name    : D1Bound5.symmetric_zero_four_adjugate_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:50.033037+00:00
-- url     : https://prove2.me/theorems/ff7b80d0-cdf8-45c9-9c7c-34a95b4a2954
-- title:
--   Symmetric zero four adjugate norm lt
-- statement:
--   The cofactor estimate holds for any symmetric zero-diagonal complex matrix, expressed without choosing or labelling its six entries.
-- source:
--   D1Bound5/AdjugateCoverage.lean, lines 80-100, SHA-256 f2847afb95c8defcb8c59c5324b1cbe3904cb7236a7d79d7d2486bba6b9076b4. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5










theorem _root_.D1Bound5.symmetric_zero_four_adjugate_norm_lt
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hzero : ∀ i, F i i = 0)
    (hsym : ∀ i j, F i j = F j i)
    (hnear : ∀ i j, i ≠ j →
      ‖F i j - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖F.adjugate‖ < productFourH * productFourS^2 := by sorry

end D1Bound5
end
