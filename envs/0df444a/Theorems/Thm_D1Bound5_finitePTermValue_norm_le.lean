-- Prove2me | Theorems.Thm_D1Bound5_finitePTermValue_norm_le
-- name    : D1Bound5.finitePTermValue_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:35:33.795147+00:00
-- url     : https://prove2.me/theorems/cf7f2854-f146-4710-9e5d-d987b9af3da3
-- title:
--   Finite PTerm Value norm le
-- statement:
--   Auxiliary result `finitePTermValue_norm_le` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePHeight.lean, lines 82-93, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePHeight_Definitions

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

















theorem _root_.D1Bound5.finitePTermValue_norm_le (a b s : ℂ) (hA : 1 ≤ ‖a‖)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (i : Fin 4) (l j t : Fin 3) :
    ‖finitePTermValue (finitePRootTerms i l j t) a b s‖ ≤
      |((finitePRootTerms i l j t).1 : ℝ)| *
        max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2) := by sorry











end D1Bound5
end
