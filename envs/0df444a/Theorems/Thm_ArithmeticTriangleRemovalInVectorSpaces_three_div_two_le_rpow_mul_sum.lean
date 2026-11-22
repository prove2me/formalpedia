-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_three_div_two_le_rpow_mul_sum
-- name    : ArithmeticTriangleRemovalInVectorSpaces.three_div_two_le_rpow_mul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:07.220626+00:00
-- url     : https://prove2.me/theorems/131aa092-e7c3-489f-ac89-d72b7387e244
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: three div two le rpow mul sum
-- statement:
--   For `0 < x < 1` and `2 ≤ p`, `3 / 2 ≤ x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean#L80-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean#L80-L96

module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
set_option autoImplicit true
@[expose] public section
public section
open Finset Filter Topology
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ}

theorem ArithmeticTriangleRemovalInVectorSpaces.three_div_two_le_rpow_mul_sum (hp : 2 ≤ p) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    3 / 2 ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j := by sorry
