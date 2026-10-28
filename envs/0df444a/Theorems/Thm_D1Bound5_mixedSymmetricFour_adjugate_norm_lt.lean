-- Prove2me | Theorems.Thm_D1Bound5_mixedSymmetricFour_adjugate_norm_lt
-- name    : D1Bound5.mixedSymmetricFour_adjugate_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:08.982301+00:00
-- url     : https://prove2.me/theorems/8df4eaa6-36bf-4468-898e-5c037552329b
-- title:
--   Mixed Symmetric Four adjugate norm lt
-- statement:
--   An unconditional L2-adjugate bound for mixed first/later cofactor radii.
-- source:
--   D1Bound5/MixedFourAdjugateBound.lean, lines 10-68, SHA-256 6b32cd9d498ea075f626860a30165f6ef389e005d96b2569ca3fea4cf0f5bd76. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.mixedSymmetricFour_adjugate_norm_lt (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
       Matrix (Fin 4) (Fin 4) ℂ).adjugate‖ <
      (155/96 : ℝ) * (59/96)^2 := by sorry



end D1Bound5
end
