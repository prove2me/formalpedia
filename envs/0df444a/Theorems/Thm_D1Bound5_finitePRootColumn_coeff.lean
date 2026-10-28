-- Prove2me | Theorems.Thm_D1Bound5_finitePRootColumn_coeff
-- name    : D1Bound5.finitePRootColumn_coeff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:32.980826+00:00
-- url     : https://prove2.me/theorems/8b9919f6-3cb2-4d2d-b395-af8368313c15
-- title:
--   Finite PRoot Column coeff
-- statement:
--   Auxiliary result `finitePRootColumn_coeff` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePHeight.lean, lines 33-43, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae. Project: https://github.com/tomislav-math/d1-bound5-lean

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











theorem _root_.D1Bound5.finitePRootColumn_coeff {R : Type*} [CommRing R]
    (a b s c : R) (i : Fin 4) (j : Fin 3) :
    finitePRootColumn a b s c i j = finitePRootCoeff a b s i 0 j +
      finitePRootCoeff a b s i 1 j*c+finitePRootCoeff a b s i 2 j*c^2 := by sorry

















end D1Bound5
end
