-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_rpow_one_sub_c
-- name    : ArithmeticTriangleRemovalInVectorSpaces.le_rpow_one_sub_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:14.624418+00:00
-- url     : https://prove2.me/theorems/963913f3-361b-470b-bf94-b65d2240463d
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: le rpow one sub c
-- statement:
--   `p ^ (1 - c p)` is the largest lower bound of `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` on
--   `Set.Ioo 0 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean#L119-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean#L119-L126

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

theorem ArithmeticTriangleRemovalInVectorSpaces.le_rpow_one_sub_c (hp : 2 ≤ p) {b : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 → b ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) :
    b ≤ (p : ℝ) ^ (1 - c p) := by sorry
