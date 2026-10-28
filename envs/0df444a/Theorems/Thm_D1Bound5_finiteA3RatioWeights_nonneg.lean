-- Prove2me | Theorems.Thm_D1Bound5_finiteA3RatioWeights_nonneg
-- name    : D1Bound5.finiteA3RatioWeights_nonneg
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:56.806312+00:00
-- url     : https://prove2.me/theorems/1e0bb5b6-1ccf-4b7c-87f7-3b3c9af39641
-- title:
--   Finite A3Ratio Weights nonneg
-- statement:
--   Auxiliary result `finiteA3RatioWeights_nonneg` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA3RatioHeight.lean, lines 16-26, SHA-256 747d84efb3a599bfd5fb9dfc2190b17d3fd8f676687d8e8b401785ccf8d1c7d7. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA3RatioHeight_Definitions

section
noncomputable section

namespace D1Bound5





theorem _root_.D1Bound5.finiteA3RatioWeights_nonneg (r : ℝ) (hr : 0 ≤ r) (i : Fin 3) (ell : Fin 4) :
    0 ≤ finiteA3RatioWeights r i ell := by sorry







end D1Bound5
end
