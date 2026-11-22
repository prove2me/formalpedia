-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_lowDegreeExponents_le
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_lowDegreeExponents_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:06.332752+00:00
-- url     : https://prove2.me/theorems/036d35b1-7dfb-424b-a831-91c524991c5d
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card low Degree Exponents le
-- statement:
--   A Chernoff bound for the number of monomials of low degree: for `0 < x ≤ 1` there are at most
--   `(x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j) ^ d` of them.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Monomials.lean#L42-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Monomials.lean#L42-L66

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Monomials
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.card_lowDegreeExponents_le {p : ℕ} (hp : 1 ≤ p) (d : ℕ) {x : ℝ} (hx₀ : 0 < x)
    (hx₁ : x ≤ 1) :
    #(lowDegreeExponents p d) ≤ (x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) ^ d := by sorry
