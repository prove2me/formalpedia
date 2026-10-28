-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_height_scaled
-- name    : D1Bound5.finiteN3_height_scaled
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:24.362587+00:00
-- url     : https://prove2.me/theorems/525b6356-f99a-4cb2-8710-ece08b0d4948
-- title:
--   Finite N3 height scaled
-- statement:
--   The actual finite N3 coefficient height with the manuscript's4143.
-- source:
--   D1Bound5/FiniteN3Height.lean, lines 104-116, SHA-256 f481f700219409141bd10895fbdbd58481a503388f7da4c50027895a33e66039. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions

section
namespace D1Bound5





















theorem _root_.D1Bound5.finiteN3_height_scaled (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN3Left x y c i‖+‖finiteN3Right x y c i‖) <
      4143*‖y‖^7*‖c‖^3 := by sorry

end D1Bound5
end
