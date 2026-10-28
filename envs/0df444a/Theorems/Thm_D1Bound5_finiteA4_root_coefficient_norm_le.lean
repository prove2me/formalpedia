-- Prove2me | Theorems.Thm_D1Bound5_finiteA4_root_coefficient_norm_le
-- name    : D1Bound5.finiteA4_root_coefficient_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:06.885625+00:00
-- url     : https://prove2.me/theorems/e6cbb739-3b7d-4bb1-a0f7-48b51aa2c56e
-- title:
--   Finite A4 root coefficient norm le
-- statement:
--   Each exact homogeneous coefficient pair has its own checked height.
-- source:
--   D1Bound5/FiniteA4Height.lean, lines 6-36, SHA-256 9a08f5646dc099fdc32895a9f25b5747a42057d2621384971697b0f7dffad0bf. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.finiteA4_root_coefficient_norm_le (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖)
    (i : Fin 3) (ell : Fin 5) :
    ‖finiteA4RootCoeff x y i 0 ell‖+‖finiteA4RootCoeff x y i 1 ell‖ ≤
      (finiteA4CoefficientSums i ell : ℝ)*‖y‖^(5+(ell : ℕ)) := by sorry









end D1Bound5
end
