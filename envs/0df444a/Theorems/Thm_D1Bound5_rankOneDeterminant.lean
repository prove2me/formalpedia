-- Prove2me | Theorems.Thm_D1Bound5_rankOneDeterminant
-- name    : D1Bound5.rankOneDeterminant
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:29.442071+00:00
-- url     : https://prove2.me/theorems/0adc7f05-aef7-4135-ac0f-cd91af7a74ad
-- title:
--   Rank One Determinant
-- statement:
--   The determinant lemma for a symmetric algebraic rank-one update in dimension four. This holds for complex vectors without conjugation.
-- source:
--   D1Bound5/RankOneDeterminantBound.lean, lines 44-63, SHA-256 b362986f164211020855cf466db1800afbbc67d831c98940ef56e24c7e348a9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.rankOneDeterminant (F : Matrix (Fin 4) (Fin 4) ℂ)
    (w : Fin 4 → ℂ) (hF : F.det ≠ 0) :
    (F + Matrix.vecMulVec w w).det =
      F.det * (1 + w ⬝ᵥ (F⁻¹ *ᵥ w)) := by sorry







end D1Bound5
end
