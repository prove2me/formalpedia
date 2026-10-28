-- Prove2me | Theorems.Thm_D1Bound5_finiteA5_height_scaled
-- name    : D1Bound5.finiteA5_height_scaled
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:51.215999+00:00
-- url     : https://prove2.me/theorems/25f4a75d-1f73-4b3f-a753-eab72f049e92
-- title:
--   Finite A5 height scaled
-- statement:
--   Actual integral A5 root-column height. No coefficient table or bound is an input hypothesis: all coefficients and the strict margin are proved.
-- source:
--   D1Bound5/FiniteA5Height.lean, lines 65-87, SHA-256 66f6a82be0fc7c80701dbd448df9ae7c22b21b575492e209dfdf4672c73c0f48. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.finiteA5_height_scaled (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA5Left x y c i‖+‖finiteA5Right x y c i‖) <
      3113013*‖y‖^12*‖c‖^5 := by sorry

end D1Bound5
end
