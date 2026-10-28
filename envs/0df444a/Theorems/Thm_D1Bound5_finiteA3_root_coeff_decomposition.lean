-- Prove2me | Theorems.Thm_D1Bound5_finiteA3_root_coeff_decomposition
-- name    : D1Bound5.finiteA3_root_coeff_decomposition
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:04.838534+00:00
-- url     : https://prove2.me/theorems/29c337a3-444b-4bce-8176-6c7cf5f6c907
-- title:
--   Finite A3 root coeff decomposition
-- statement:
--   Auxiliary result `finiteA3_root_coeff_decomposition` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA3Coefficients.lean, lines 21-29, SHA-256 7440cce2f6cdd37d87275749638987bd7427e186ac1d7f24fa8ba39b953689c0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions

section
namespace D1Bound5











theorem _root_.D1Bound5.finiteA3_root_coeff_decomposition {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteA3Left x y c i,finiteA3Right x y c i] j =
      ∑ ell : Fin 4, finiteA3RootCoeff x y i j ell*c^(ell : ℕ) := by sorry











end D1Bound5
end
