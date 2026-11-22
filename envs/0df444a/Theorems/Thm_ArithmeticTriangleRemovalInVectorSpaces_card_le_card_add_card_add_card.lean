-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_le_card_add_card_add_card
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_le_card_add_card_add_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:09.972946+00:00
-- url     : https://prove2.me/theorems/18437a8d-840d-4c9a-894f-bde736e6a825
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card le card add card add card
-- statement:
--   **Tao's lemma** on the slice rank of a diagonal tensor. If the function
--   `fun i j k ↦ if i = j ∧ j = k then 1 else 0` on `ι × ι × ι` is a sum of `#A + #B + #C` products,
--   each of a function of one variable and a function of the other two, then `ι` has at most
--   `#A + #B + #C` elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/SliceRank/Diagonal.lean#L120-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/SliceRank/Diagonal.lean#L120-L128

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_SliceRank_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Finset Matrix Module
open ArithmeticTriangleRemovalInVectorSpaces
variable {ι F : Type*} [Fintype ι] [Field F]

theorem ArithmeticTriangleRemovalInVectorSpaces.card_le_card_add_card_add_card [DecidableEq ι] {α β γ : Type*} {A : Finset α} {B : Finset β}
    {C : Finset γ} (f : α → ι → F) (g : α → ι → ι → F) (f' : β → ι → F) (g' : β → ι → ι → F)
    (f'' : γ → ι → F) (g'' : γ → ι → ι → F)
    (h : ∀ i j k, (if i = j ∧ j = k then 1 else 0 : F) =
      ∑ a ∈ A, f a i * g a j k + ∑ b ∈ B, f' b j * g' b i k + ∑ c ∈ C, f'' c k * g'' c i j) :
    Fintype.card ι ≤ #A + #B + #C := by sorry
