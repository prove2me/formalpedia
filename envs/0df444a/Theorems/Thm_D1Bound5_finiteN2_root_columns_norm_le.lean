-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_root_columns_norm_le
-- name    : D1Bound5.finiteN2_root_columns_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:27.639123+00:00
-- url     : https://prove2.me/theorems/add07305-3ec8-4e0b-9ca1-82be68910b6c
-- title:
--   Finite N2 root columns norm le
-- statement:
--   Auxiliary result `finiteN2_root_columns_norm_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteN2Height.lean, lines 48-73, SHA-256 2243c6283cc2715ea06a1ac894af3fc0ea0e8e3a907fae2e4dc3a502c1037c77. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions

section
namespace D1Bound5











theorem _root_.D1Bound5.finiteN2_root_columns_norm_le (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖ ≤
      50*‖y‖^2+200*‖y‖^3*‖c‖+240*‖y‖^4*‖c‖^2 := by sorry





end D1Bound5
end
