-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_root_coeff_decomposition
-- name    : D1Bound5.finiteN2_root_coeff_decomposition
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:59.316042+00:00
-- url     : https://prove2.me/theorems/cdd593ec-a4fe-4898-9373-e0ce41489cf4
-- title:
--   Finite N2 root coeff decomposition
-- statement:
--   Exact homogeneous decomposition of both divided root columns.
-- source:
--   D1Bound5/FiniteN2Height.lean, lines 23-34, SHA-256 2243c6283cc2715ea06a1ac894af3fc0ea0e8e3a907fae2e4dc3a502c1037c77. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions

section
namespace D1Bound5








theorem _root_.D1Bound5.finiteN2_root_coeff_decomposition {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteN2Left x y c i, finiteN2Right x y c i] j =
      finiteHomogeneousTwo 2 (finiteN2Coeff0 i j) x y +
      finiteHomogeneousTwo 3 (finiteN2Coeff1 i j) x y*c +
      finiteHomogeneousTwo 4 (finiteN2Coeff2 i j) x y*c^2 := by sorry









end D1Bound5
end
