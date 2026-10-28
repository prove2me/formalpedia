-- Prove2me | Theorems.Thm_D1Bound5_halfOffDiagonal_adjugate_apply
-- name    : D1Bound5.halfOffDiagonal_adjugate_apply
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:01.124097+00:00
-- url     : https://prove2.me/theorems/5a1395c6-9035-4d87-a744-2bb8ac248eb0
-- title:
--   Half Off Diagonal adjugate apply
-- statement:
--   Exact cofactors at the reference matrix: diagonal 1/4, otherwise -1/8.
-- source:
--   D1Bound5/ReferenceMatrixSpectral.lean, lines 80-89, SHA-256 a9d2534dbab31dc06c160d4476f3546ac57b74623f0a03cba8eaeb8e7e822001. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

















theorem _root_.D1Bound5.halfOffDiagonal_adjugate_apply (i j : Fin 4) :
    halfOffDiagonal.adjugate i j =
      if i = j then (1/4 : ℂ) else (-1/8 : ℂ) := by sorry

end D1Bound5
end
