-- Prove2me | Theorems.Thm_D1Bound5_finiteA4_root_coeff_decomposition
-- name    : D1Bound5.finiteA4_root_coeff_decomposition
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:27.195866+00:00
-- url     : https://prove2.me/theorems/89403a70-ecb8-441b-8b00-7d51cb25acd2
-- title:
--   Finite A4 root coeff decomposition
-- statement:
--   Auxiliary result `finiteA4_root_coeff_decomposition` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteA4Coefficients.lean, lines 24-32, SHA-256 81e084e83fa4d83f09a896a30127692abe2447284beb04da6e2eb20845e20c86. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions

section
namespace D1Bound5













theorem _root_.D1Bound5.finiteA4_root_coeff_decomposition {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteA4Left x y c i,finiteA4Right x y c i] j =
      ∑ ell : Fin 5, finiteA4RootCoeff x y i j ell*c^(ell : ℕ) := by sorry













end D1Bound5
end
