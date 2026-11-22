-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_triangles_nonempty_of_card_sdiff_add_lt
-- name    : ArithmeticTriangleRemovalInVectorSpaces.triangles_nonempty_of_card_sdiff_add_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:28.319208+00:00
-- url     : https://prove2.me/theorems/9eeacd89-87ec-44be-9c54-237c9f7e08fc
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: triangles nonempty of card sdiff add lt
-- statement:
--   Removing fewer than `m` elements from the vertex sets of `m` vertex-disjoint triangles leaves a
--   triangle.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L86-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L86-L103

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
variable [DecidableEq G] [Fintype ι]

theorem ArithmeticTriangleRemovalInVectorSpaces.triangles_nonempty_of_card_sdiff_add_lt (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hsum : ∀ i, x i + y i + z i = 0) {X Y Z : Finset G}
    (hcard : #(univ.image x \ X) + #(univ.image y \ Y) + #(univ.image z \ Z) < Fintype.card ι) :
    (triangles X Y Z).Nonempty := by sorry
