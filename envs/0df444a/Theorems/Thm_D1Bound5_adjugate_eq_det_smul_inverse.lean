-- Prove2me | Theorems.Thm_D1Bound5_adjugate_eq_det_smul_inverse
-- name    : D1Bound5.adjugate_eq_det_smul_inverse
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:29.254004+00:00
-- url     : https://prove2.me/theorems/5c8c8b31-894a-4d62-aa8c-cc381fde5cee
-- title:
--   Adjugate eq det smul inverse
-- statement:
--   Express the adjugate of an invertible matrix in terms of its inverse.
-- source:
--   D1Bound5/RankOneDeterminantBound.lean, lines 65-75, SHA-256 b362986f164211020855cf466db1800afbbc67d831c98940ef56e24c7e348a9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.adjugate_eq_det_smul_inverse (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : F.det ≠ 0) : F.adjugate = F.det • F⁻¹ := by sorry





end D1Bound5
end
