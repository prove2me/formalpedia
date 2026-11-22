-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_card_le_three_mul_card
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_three_mul_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:09.717825+00:00
-- url     : https://prove2.me/theorems/9220d65d-a266-40ea-ab0b-4dbd94785b50
-- title:
--   Is Multicolored Sum Free: card le three mul card
-- statement:
--   **The slice rank bound** for multicolored sum-free families: a multicolored sum-free family in
--   `Fin d → ZMod p` has at most `3 * #(lowDegreeExponents p d)` members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/SliceRank.lean#L167-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/SliceRank.lean#L167-L179

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Monomials
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_SliceRank_Diagonal
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.FieldTheory.Finite.Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SliceRank
set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime]

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_le_three_mul_card {ι : Type*} [Fintype ι] {d : ℕ}
    {x y z : ι → Fin d → ZMod p} (h : IsMulticoloredSumFree x y z) :
    Fintype.card ι ≤ 3 * #(lowDegreeExponents p d) := by sorry
