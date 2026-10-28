-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_coefficient_sums
-- name    : D1Bound5.finiteN2_coefficient_sums
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:58.233744+00:00
-- url     : https://prove2.me/theorems/cd04ee27-a2d1-4ffb-9b71-1456f4fc5c3e
-- title:
--   Finite N2 coefficient sums
-- statement:
--   The coefficient sums are computed from the actual integer vectors, not supplied as table data in a hypothesis.
-- source:
--   D1Bound5/FiniteN2Height.lean, lines 36-46, SHA-256 2243c6283cc2715ea06a1ac894af3fc0ea0e8e3a907fae2e4dc3a502c1037c77. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.finiteN2_coefficient_sums (i : Fin 3) :
    ((∑ j, |(finiteN2Coeff0 i 0 j : ℝ)|) +
      (∑ j, |(finiteN2Coeff0 i 1 j : ℝ)|) ≤ 50) ∧
    ((∑ j, |(finiteN2Coeff1 i 0 j : ℝ)|) +
      (∑ j, |(finiteN2Coeff1 i 1 j : ℝ)|) ≤ 200) ∧
    ((∑ j, |(finiteN2Coeff2 i 0 j : ℝ)|) +
      (∑ j, |(finiteN2Coeff2 i 1 j : ℝ)|) ≤ 240) := by sorry







end D1Bound5
end
