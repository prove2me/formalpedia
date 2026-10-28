-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_root_columns_norm_le
-- name    : D1Bound5.finiteN3_root_columns_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:24:45.585177+00:00
-- url     : https://prove2.me/theorems/d9cc1fc1-7b39-466d-8fbe-455427e10210
-- title:
--   Finite N3 root columns norm le
-- statement:
--   Auxiliary result `finiteN3_root_columns_norm_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteN3Height.lean, lines 66-95, SHA-256 f481f700219409141bd10895fbdbd58481a503388f7da4c50027895a33e66039. Project: https://github.com/tomislav-math/d1-bound5-lean

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
















theorem _root_.D1Bound5.finiteN3_root_columns_norm_le (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteN3Left x y c i‖+‖finiteN3Right x y c i‖ ≤
      342*‖y‖^4+2352*‖y‖^5*‖c‖+5792*‖y‖^6*‖c‖^2+4096*‖y‖^7*‖c‖^3 := by sorry





end D1Bound5
end
