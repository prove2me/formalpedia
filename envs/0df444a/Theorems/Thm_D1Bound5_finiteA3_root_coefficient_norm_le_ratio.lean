-- Prove2me | Theorems.Thm_D1Bound5_finiteA3_root_coefficient_norm_le_ratio
-- name    : D1Bound5.finiteA3_root_coefficient_norm_le_ratio
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:57.183006+00:00
-- url     : https://prove2.me/theorems/c3991ecf-2924-4a75-bb0e-323ca644b6ea
-- title:
--   Finite A3 root coefficient norm le ratio
-- statement:
--   Auxiliary result `finiteA3_root_coefficient_norm_le_ratio` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA3RatioHeight.lean, lines 28-48, SHA-256 747d84efb3a599bfd5fb9dfc2190b17d3fd8f676687d8e8b401785ccf8d1c7d7. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA3RatioHeight_Definitions

section
noncomputable section

namespace D1Bound5







theorem _root_.D1Bound5.finiteA3_root_coefficient_norm_le_ratio (x y : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hxy : ‖x‖ ≤ r*‖y‖) (i : Fin 3) (ell : Fin 4) :
    ‖finiteA3RootCoeff x y i 0 ell‖+‖finiteA3RootCoeff x y i 1 ell‖ ≤
      finiteA3RatioWeights r i ell*‖y‖^(3+(ell : ℕ)) := by sorry





end D1Bound5
end
