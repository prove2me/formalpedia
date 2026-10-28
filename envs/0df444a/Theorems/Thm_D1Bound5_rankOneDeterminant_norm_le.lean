-- Prove2me | Theorems.Thm_D1Bound5_rankOneDeterminant_norm_le
-- name    : D1Bound5.rankOneDeterminant_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:46.775107+00:00
-- url     : https://prove2.me/theorems/dc4fcb26-6b2e-4371-97d3-292028bce7c2
-- title:
--   Rank One Determinant norm le
-- statement:
--   Determinant bound for a rank-one update, using the inverse norm.
-- source:
--   D1Bound5/RankOneDeterminantBound.lean, lines 77-96, SHA-256 b362986f164211020855cf466db1800afbbc67d831c98940ef56e24c7e348a9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.rankOneDeterminant_norm_le (F : Matrix (Fin 4) (Fin 4) ℂ)
    (w : Fin 4 → ℂ) (hF : F.det ≠ 0) :
    ‖(F + Matrix.vecMulVec w w).det‖ ≤
      ‖F.det‖ * (1 + ‖F⁻¹‖ * (∑ i, ‖w i‖ ^ 2)) := by sorry



end D1Bound5
end
