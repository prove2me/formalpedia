-- Prove2me | Theorems.Thm_D1Bound5_finiteA5_root_coefficient_norm_le
-- name    : D1Bound5.finiteA5_root_coefficient_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:43.149175+00:00
-- url     : https://prove2.me/theorems/b81e2bff-2d33-4504-97a1-4fe2a8424a9d
-- title:
--   Finite A5 root coefficient norm le
-- statement:
--   Each exact homogeneous coefficient pair has its own checked height.
-- source:
--   D1Bound5/FiniteA5Height.lean, lines 6-41, SHA-256 66f6a82be0fc7c80701dbd448df9ae7c22b21b575492e209dfdf4672c73c0f48. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.finiteA5_root_coefficient_norm_le (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖)
    (i : Fin 3) (ell : Fin 6) :
    ‖finiteA5RootCoeff x y i 0 ell‖+‖finiteA5RootCoeff x y i 1 ell‖ ≤
      (finiteA5CoefficientSums i ell : ℝ)*‖y‖^(7+(ell : ℕ)) := by sorry









end D1Bound5
end
