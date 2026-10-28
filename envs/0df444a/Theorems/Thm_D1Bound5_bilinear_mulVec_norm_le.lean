-- Prove2me | Theorems.Thm_D1Bound5_bilinear_mulVec_norm_le
-- name    : D1Bound5.bilinear_mulVec_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:35.144654+00:00
-- url     : https://prove2.me/theorems/a2c26737-91a8-4943-8869-adc9a0b5031c
-- title:
--   Bilinear mul Vec norm le
-- statement:
--   The modulus of a complex bilinear quadratic form is bounded by the Euclidean operator norm. No Hermitian or symmetry assumption is needed.
-- source:
--   D1Bound5/RankOneDeterminantBound.lean, lines 11-42, SHA-256 b362986f164211020855cf466db1800afbbc67d831c98940ef56e24c7e348a9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.bilinear_mulVec_norm_le (F : Matrix (Fin 4) (Fin 4) ℂ)
    (w : Fin 4 → ℂ) :
    ‖w ⬝ᵥ (F *ᵥ w)‖ ≤ ‖F‖ * (∑ i, ‖w i‖ ^ 2) := by sorry









end D1Bound5
end
