-- Prove2me | Theorems.Thm_D1Bound5_finiteN3RatioWeights_nonneg
-- name    : D1Bound5.finiteN3RatioWeights_nonneg
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:54.555741+00:00
-- url     : https://prove2.me/theorems/54a4765a-c604-4e69-89f4-294a514050d3
-- title:
--   Finite N3Ratio Weights nonneg
-- statement:
--   Auxiliary result `finiteN3RatioWeights_nonneg` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteN3RatioHeight.lean, lines 30-40, SHA-256 3b19adaab7a046dd5d462fa93e9c3522cc668117966f660bde17388fd5b6b587. Project: https://github.com/tomislav-math/d1-bound5-lean

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









theorem _root_.D1Bound5.finiteN3RatioWeights_nonneg (r : ℝ) (hr : 0 ≤ r) (i : Fin 3) (ell : Fin 4) :
    0 ≤ finiteN3RatioWeights r i ell := by sorry







end D1Bound5
end
