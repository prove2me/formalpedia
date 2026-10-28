-- Prove2me | Theorems.Thm_D1Bound5_rankOneDeterminant_adjugate_norm_le
-- name    : D1Bound5.rankOneDeterminant_adjugate_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:24.573708+00:00
-- url     : https://prove2.me/theorems/8aae2c9a-13e5-45f9-a164-70d478483acf
-- title:
--   Rank One Determinant adjugate norm le
-- statement:
--   The rank-one determinant bound in precisely the cofactor form required by the determinant argument in lem:product-four.
-- source:
--   D1Bound5/RankOneDeterminantBound.lean, lines 98-112, SHA-256 b362986f164211020855cf466db1800afbbc67d831c98940ef56e24c7e348a9c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator
open scoped InnerProductSpace
open Matrix

namespace D1Bound5










theorem _root_.D1Bound5.rankOneDeterminant_adjugate_norm_le (F : Matrix (Fin 4) (Fin 4) ℂ)
    (w : Fin 4 → ℂ) (hF : F.det ≠ 0) :
    ‖(F + Matrix.vecMulVec w w).det‖ ≤
      ‖F.det‖ + ‖F.adjugate‖ * (∑ i, ‖w i‖ ^ 2) := by sorry

end D1Bound5
end
