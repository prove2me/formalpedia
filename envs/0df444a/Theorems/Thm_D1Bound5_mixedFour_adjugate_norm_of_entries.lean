-- Prove2me | Theorems.Thm_D1Bound5_mixedFour_adjugate_norm_of_entries
-- name    : D1Bound5.mixedFour_adjugate_norm_of_entries
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:14:29.697717+00:00
-- url     : https://prove2.me/theorems/cbef3b84-8ec4-4e79-8a34-47ff77b2b948
-- title:
--   Mixed Four adjugate norm of entries
-- statement:
--   Weighted Schur closure for all 16 distinct mixed adjugate entries.
-- source:
--   D1Bound5/MixedAdjugateEnvelope.lean, lines 41-84, SHA-256 f452ef49f0d5283120370edce69efeffabb48f22241346c2ec9821c339c43131. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5










theorem _root_.D1Bound5.mixedFour_adjugate_norm_of_entries
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hdiag : ∀ i, ‖(F.adjugate - halfOffDiagonal.adjugate) i i‖ <
      if i = 0 then (1/40 : ℝ) else 7/100)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖(F.adjugate - halfOffDiagonal.adjugate) i j‖ < (53/1000 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖(F.adjugate - halfOffDiagonal.adjugate) i j‖ < (47/1000 : ℝ)) :
    ‖F.adjugate‖ < (155/96 : ℝ) * (59/96)^2 := by sorry

end D1Bound5
end
