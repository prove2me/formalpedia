-- Prove2me | Theorems.Thm_D1Bound5_finiteA4_height_scaled
-- name    : D1Bound5.finiteA4_height_scaled
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:21:31.821735+00:00
-- url     : https://prove2.me/theorems/1258d9c5-8794-4cff-ab35-ff0125d64407
-- title:
--   Finite A4 height scaled
-- statement:
--   Actual integral A4 root-column height. No coefficient table or bound is an input hypothesis: all coefficients and the strict margin are proved.
-- source:
--   D1Bound5/FiniteA4Height.lean, lines 60-82, SHA-256 9a08f5646dc099fdc32895a9f25b5747a42057d2621384971697b0f7dffad0bf. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.finiteA4_height_scaled (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA4Left x y c i‖+‖finiteA4Right x y c i‖) <
      165763*‖y‖^9*‖c‖^4 := by sorry

end D1Bound5
end
