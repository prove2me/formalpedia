-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_root_coefficient_norm_le_ratio
-- name    : D1Bound5.finiteN2_root_coefficient_norm_le_ratio
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:48.572556+00:00
-- url     : https://prove2.me/theorems/7d2fbb6f-0f91-4ef5-9d73-c98906c17cf1
-- title:
--   Finite N2 root coefficient norm le ratio
-- statement:
--   Auxiliary result `finiteN2_root_coefficient_norm_le_ratio` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteN2RatioHeight.lean, lines 38-54, SHA-256 acd86dd6afa56a2834a76abb67f2f38aa493cf97b505b550e022ae5087305669. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2RatioHeight_Definitions

section
noncomputable section

namespace D1Bound5











theorem _root_.D1Bound5.finiteN2_root_coefficient_norm_le_ratio (x y : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ‖x‖ ≤ r*‖y‖) (i : Fin 3) (ell : Fin 3) :
    ‖finiteN2RatioRootCoeff x y i 0 ell‖+‖finiteN2RatioRootCoeff x y i 1 ell‖ ≤
      finiteN2RatioWeights r i ell*‖y‖^(2+(ell : ℕ)) := by sorry





end D1Bound5
end
