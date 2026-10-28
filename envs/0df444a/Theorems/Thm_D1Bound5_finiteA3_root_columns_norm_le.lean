-- Prove2me | Theorems.Thm_D1Bound5_finiteA3_root_columns_norm_le
-- name    : D1Bound5.finiteA3_root_columns_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:44:59.388868+00:00
-- url     : https://prove2.me/theorems/66af4b20-b220-4692-86c7-74e11f00c50e
-- title:
--   Finite A3 root columns norm le
-- statement:
--   Auxiliary result `finiteA3_root_columns_norm_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA3Height.lean, lines 43-53, SHA-256 f804d9c0c6b4a710739b80930e84355ca29a061e137634a0fae8411054c3b698. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions

section
namespace D1Bound5







theorem _root_.D1Bound5.finiteA3_root_columns_norm_le (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteA3Left x y c i‖+‖finiteA3Right x y c i‖ ≤
      ‖y‖^3*∑ ell : Fin 4, (finiteA3CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ) := by sorry



end D1Bound5
end
