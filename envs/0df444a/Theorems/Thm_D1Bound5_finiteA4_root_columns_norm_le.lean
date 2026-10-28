-- Prove2me | Theorems.Thm_D1Bound5_finiteA4_root_columns_norm_le
-- name    : D1Bound5.finiteA4_root_columns_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:39:22.378916+00:00
-- url     : https://prove2.me/theorems/bb9673e4-d67b-41ca-a9dd-b8f05d5c9a9e
-- title:
--   Finite A4 root columns norm le
-- statement:
--   Auxiliary result `finiteA4_root_columns_norm_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA4Height.lean, lines 48-58, SHA-256 9a08f5646dc099fdc32895a9f25b5747a42057d2621384971697b0f7dffad0bf. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions

section
namespace D1Bound5







theorem _root_.D1Bound5.finiteA4_root_columns_norm_le (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteA4Left x y c i‖+‖finiteA4Right x y c i‖ ≤
      ‖y‖^5*∑ ell : Fin 5, (finiteA4CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ) := by sorry



end D1Bound5
end
