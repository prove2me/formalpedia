-- Prove2me | Theorems.Thm_D1Bound5_finiteN3_root_coeff_decomposition
-- name    : D1Bound5.finiteN3_root_coeff_decomposition
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:24:45.750987+00:00
-- url     : https://prove2.me/theorems/4a161a6b-d90e-4691-8240-78fc6da49f9b
-- title:
--   Finite N3 root coeff decomposition
-- statement:
--   Exact coefficient vectors, checked against the actual N3 matrix.
-- source:
--   D1Bound5/FiniteN3Height.lean, lines 38-50, SHA-256 f481f700219409141bd10895fbdbd58481a503388f7da4c50027895a33e66039. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions

section
namespace D1Bound5













theorem _root_.D1Bound5.finiteN3_root_coeff_decomposition {R : Type*} [CommRing R]
    (x y c : R) (i : Fin 3) (j : Fin 2) :
    ![finiteN3Left x y c i,finiteN3Right x y c i] j =
      finiteHomogeneousTwo 4 (finiteN3Coeff0 i j) x y +
      finiteHomogeneousTwo 5 (finiteN3Coeff1 i j) x y*c +
      finiteHomogeneousTwo 6 (finiteN3Coeff2 i j) x y*c^2 +
      finiteHomogeneousTwo 7 (finiteN3Coeff3 i j) x y*c^3 := by sorry









end D1Bound5
end
