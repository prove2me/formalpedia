-- Prove2me | Theorems.Thm_D1Bound5_exists_small_root_error
-- name    : D1Bound5.exists_small_root_error
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:08.429997+00:00
-- url     : https://prove2.me/theorems/99f4c6a5-b23d-42da-85a6-47a2e3d73940
-- title:
--   Exists small root error
-- statement:
--   A sign of every complex square root of x(x+1), when |x| >= 9, has correction strictly within 16/31 of zero and 128/8649 of 1/2. This is the branch-selection part of (integrated-1)--(integrated-2); the constants are uniform and do not require an analytic square root.
-- source:
--   D1Bound5/RootErrorMagnitude.lean, lines 8-68, SHA-256 090472365e3db009e37be35676f898eae037822776991930233fc88ea690af2b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.exists_small_root_error (x t : ℂ)
    (hx : 9 ≤ ‖x‖) (ht : t^2 = x*(x+1)) :
    ∃ v : ℂ, (v = t ∨ v = -t) ∧
      ‖v-x‖ < (16/31 : ℝ) ∧
      ‖(v-x)-(1/2 : ℂ)‖ < (128/8649 : ℝ) := by sorry










end D1Bound5
end
