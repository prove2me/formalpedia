-- Prove2me | Theorems.Thm_D1Bound5_exists_small_normalized_root_error
-- name    : D1Bound5.exists_small_normalized_root_error
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:25.789613+00:00
-- url     : https://prove2.me/theorems/7eaf2566-b70d-4cb6-9e39-475f560c3dd3
-- title:
--   Exists small normalized root error
-- statement:
--   The same choice for normalized off-diagonal entries of an integral root matrix. Only complex algebra is used at this stage.
-- source:
--   D1Bound5/RootErrorMagnitude.lean, lines 70-81, SHA-256 090472365e3db009e37be35676f898eae037822776991930233fc88ea690af2b. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.exists_small_normalized_root_error (a b u v r : ℂ)
    (hu : u^2=a) (hv : v^2=b) (hr : r^2=a*b+1)
    (hab : 9 ≤ ‖a*b‖) :
    ∃ t : ℂ, (t=u*r*v ∨ t=-(u*r*v)) ∧
      ‖t-a*b‖ < (16/31 : ℝ) ∧
      ‖(t-a*b)-(1/2 : ℂ)‖ < (128/8649 : ℝ) := by sorry








end D1Bound5
end
