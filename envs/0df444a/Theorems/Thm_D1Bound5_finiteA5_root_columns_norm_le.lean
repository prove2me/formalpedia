-- Prove2me | Theorems.Thm_D1Bound5_finiteA5_root_columns_norm_le
-- name    : D1Bound5.finiteA5_root_columns_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:48:01.301699+00:00
-- url     : https://prove2.me/theorems/2c20d746-6d86-4937-866b-57e049b4e4f7
-- title:
--   Finite A5 root columns norm le
-- statement:
--   Auxiliary result `finiteA5_root_columns_norm_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA5Height.lean, lines 53-63, SHA-256 66f6a82be0fc7c80701dbd448df9ae7c22b21b575492e209dfdf4672c73c0f48. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions

section
namespace D1Bound5







theorem _root_.D1Bound5.finiteA5_root_columns_norm_le (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteA5Left x y c i‖+‖finiteA5Right x y c i‖ ≤
      ‖y‖^7*∑ ell : Fin 6, (finiteA5CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ) := by sorry



end D1Bound5
end
