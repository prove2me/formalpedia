-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_card_triangles_prod
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_triangles_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:16.998244+00:00
-- url     : https://prove2.me/theorems/b3a2e58e-a8cd-49b1-9047-7733f556feaa
-- title:
--   Is Multicolored Sum Free: card triangles prod
-- statement:
--   The sets `X × W`, `Y × W` and `Z × W` built from a multicolored sum-free family of `m` triples
--   contain `m * #W ^ 2` triangles.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L111-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L111-L132

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Abel
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {ι G W : Type*} [AddCommGroup G] [AddCommGroup W] {x y z : ι → G}
variable [DecidableEq G] [DecidableEq W] [Fintype ι] [Fintype W]

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.card_triangles_prod (h : IsMulticoloredSumFree x y z) :
    #(triangles (univ.image x ×ˢ (univ : Finset W)) (univ.image y ×ˢ univ) (univ.image z ×ˢ univ))
      = Fintype.card ι * Fintype.card W ^ 2 := by sorry
