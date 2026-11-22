-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_rpow_one_sub_c_le
-- name    : ArithmeticTriangleRemovalInVectorSpaces.rpow_one_sub_c_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:15.310407+00:00
-- url     : https://prove2.me/theorems/ba3654d3-1185-41a2-b6bc-4f03ab03ed20
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: rpow one sub c le
-- statement:
--   `p ^ (1 - c p)` is at most `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` for `0 < x < 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean#L110-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean#L110-L115

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

theorem ArithmeticTriangleRemovalInVectorSpaces.rpow_one_sub_c_le (hp : 2 ≤ p) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    (p : ℝ) ^ (1 - c p) ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j := by sorry
