-- Prove2me | Theorems.Thm_D1Bound5_finiteA3_root_coefficient_norm_le
-- name    : D1Bound5.finiteA3_root_coefficient_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:59.104557+00:00
-- url     : https://prove2.me/theorems/17f1eeea-3e31-42f4-958e-356ee8c66430
-- title:
--   Finite A3 root coefficient norm le
-- statement:
--   Each exact homogeneous coefficient pair has its own checked height.
-- source:
--   D1Bound5/FiniteA3Height.lean, lines 6-31, SHA-256 f804d9c0c6b4a710739b80930e84355ca29a061e137634a0fae8411054c3b698. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.finiteA3_root_coefficient_norm_le (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖)
    (i : Fin 3) (ell : Fin 4) :
    ‖finiteA3RootCoeff x y i 0 ell‖+‖finiteA3RootCoeff x y i 1 ell‖ ≤
      (finiteA3CoefficientSums i ell : ℝ)*‖y‖^(3+(ell : ℕ)) := by sorry









end D1Bound5
end
