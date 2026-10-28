-- Prove2me | Theorems.Thm_D1Bound5_integral_basis_one_gcd
-- name    : D1Bound5.integral_basis_one_gcd
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:34:11.378572+00:00
-- url     : https://prove2.me/theorems/5f28964e-dfe5-491e-9ff8-12a1ee4d4198
-- title:
--   Integral basis one gcd
-- statement:
--   The two coordinates of one in any integral basis are coprime.
-- source:
--   D1Bound5/FullRingBasis.lean, lines 14-39, SHA-256 7a7a55f350ab7d5224275914efa11b126ec34a9ae9cc9e505c2669503411924c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K]


theorem _root_.D1Bound5.integral_basis_one_gcd (hK : finrank ℚ K = 2)
    (B : Basis (Fin 2) ℤ (𝓞 K)) :
    Int.gcd (B.repr 1 0) (B.repr 1 1) = 1 := by sorry








end D1Bound5
end
