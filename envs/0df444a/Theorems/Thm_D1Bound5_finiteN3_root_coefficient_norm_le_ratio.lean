-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_root_coefficient_norm_le_ratio
-- name    : D1Bound5.finiteN3_root_coefficient_norm_le_ratio
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:26:14.939146+00:00
-- url     : https://prove2.me/theorems/d3043b69-c9aa-4f02-ac57-ec71dd5c87c6
-- title:
--   Finite N3 root coefficient norm le ratio
-- statement:
--   Auxiliary result `finiteN3_root_coefficient_norm_le_ratio` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteN3RatioHeight.lean, lines 42-62, SHA-256 3b19adaab7a046dd5d462fa93e9c3522cc668117966f660bde17388fd5b6b587. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN3RatioHeight_Definitions

section
noncomputable section

namespace D1Bound5











theorem _root_.D1Bound5.finiteN3_root_coefficient_norm_le_ratio (x y : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ‖x‖ ≤ r*‖y‖) (i : Fin 3) (ell : Fin 4) :
    ‖finiteN3RatioRootCoeff x y i 0 ell‖+‖finiteN3RatioRootCoeff x y i 1 ell‖ ≤
      finiteN3RatioWeights r i ell*‖y‖^(4+(ell : ℕ)) := by sorry





end D1Bound5
end
