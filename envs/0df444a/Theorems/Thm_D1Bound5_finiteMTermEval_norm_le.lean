-- Prove2me | Theorems.Thm_D1Bound5_finiteMTermEval_norm_le
-- name    : D1Bound5.finiteMTermEval_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:35.130127+00:00
-- url     : https://prove2.me/theorems/d8ac71d4-4acb-41b6-a01a-2538499384a4
-- title:
--   Finite MTerm Eval norm le
-- statement:
--   A single factored integer monomial has the advertised weighted height. The admissibility condition is discharged for every actual term by a finite natural-number certificate in FiniteMMatrix.
-- source:
--   D1Bound5/FiniteMHeight.lean, lines 34-67, SHA-256 6928941a5a34ad2fa5a5df87a96078a75cfb91e880665ed0fbfc978d07ef85b6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.finiteMTermEval_norm_le (t : FiniteMTerm) (a b s v : ℂ)
    (B S C : ℝ) (hB : 1 ≤ B) (hBS : B ≤ S) (hC : 1 ≤ C)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hs : ‖s‖ ≤ S)
    (hv : ‖v‖ ≤ 2*S*C) (ht : finiteMTermAdmissible t) :
    ‖finiteMTermEval t a b s v‖ ≤ (finiteMTermWeight t : ℝ)*B^3*S^8*C^2 := by sorry





end D1Bound5
end
