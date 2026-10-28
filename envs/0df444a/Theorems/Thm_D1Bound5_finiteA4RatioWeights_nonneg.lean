-- Prove2me | Theorems.Thm_D1Bound5_finiteA4RatioWeights_nonneg
-- name    : D1Bound5.finiteA4RatioWeights_nonneg
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:25:19.693622+00:00
-- url     : https://prove2.me/theorems/d7f39932-6f2b-4d05-8b6b-b98a79772af2
-- title:
--   Finite A4Ratio Weights nonneg
-- statement:
--   Auxiliary result `finiteA4RatioWeights_nonneg` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA4RatioHeight.lean, lines 17-29, SHA-256 a98d9593d896e1b8a0048726d24791b93b2bacc8fb14d4196e608cc3b8ddd02c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4RatioHeight_Definitions

section
noncomputable section

namespace D1Bound5





theorem _root_.D1Bound5.finiteA4RatioWeights_nonneg (r : ℝ) (hr : 0 ≤ r) (i : Fin 3) (ell : Fin 5) :
    0 ≤ finiteA4RatioWeights r i ell := by sorry







end D1Bound5
end
