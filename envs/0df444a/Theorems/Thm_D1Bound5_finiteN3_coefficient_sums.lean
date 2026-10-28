-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_coefficient_sums
-- name    : D1Bound5.finiteN3_coefficient_sums
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:38.890349+00:00
-- url     : https://prove2.me/theorems/b2eaa0c8-7901-450a-8a3a-f3a80e531848
-- title:
--   Finite N3 coefficient sums
-- statement:
--   Integer coefficient sums computed from the actual vectors. Taking the maximum separately in each degree still leaves strict slack at4143.
-- source:
--   D1Bound5/FiniteN3Height.lean, lines 52-64, SHA-256 f481f700219409141bd10895fbdbd58481a503388f7da4c50027895a33e66039. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions

section
namespace D1Bound5















theorem _root_.D1Bound5.finiteN3_coefficient_sums (i : Fin 3) :
    ((∑ j, |(finiteN3Coeff0 i 0 j : ℝ)|)+
      (∑ j, |(finiteN3Coeff0 i 1 j : ℝ)|) ≤ 342) ∧
    ((∑ j, |(finiteN3Coeff1 i 0 j : ℝ)|)+
      (∑ j, |(finiteN3Coeff1 i 1 j : ℝ)|) ≤ 2352) ∧
    ((∑ j, |(finiteN3Coeff2 i 0 j : ℝ)|)+
      (∑ j, |(finiteN3Coeff2 i 1 j : ℝ)|) ≤ 5792) ∧
    ((∑ j, |(finiteN3Coeff3 i 0 j : ℝ)|)+
      (∑ j, |(finiteN3Coeff3 i 1 j : ℝ)|) ≤ 4096) := by sorry







end D1Bound5
end
