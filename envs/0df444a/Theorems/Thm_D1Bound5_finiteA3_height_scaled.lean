-- Prove2me | Theorems.Thm_D1Bound5_finiteA3_height_scaled
-- name    : D1Bound5.finiteA3_height_scaled
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:04.550249+00:00
-- url     : https://prove2.me/theorems/faaf3183-924b-42c1-8675-1bbe18457f32
-- title:
--   Finite A3 height scaled
-- statement:
--   Actual integral A3 root-column height. No coefficient table or bound is an input hypothesis: all coefficients and the strict margin are proved.
-- source:
--   D1Bound5/FiniteA3Height.lean, lines 55-77, SHA-256 f804d9c0c6b4a710739b80930e84355ca29a061e137634a0fae8411054c3b698. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.finiteA3_height_scaled (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA3Left x y c i‖+‖finiteA3Right x y c i‖) <
      2265*‖y‖^6*‖c‖^3 := by sorry

end D1Bound5
end
