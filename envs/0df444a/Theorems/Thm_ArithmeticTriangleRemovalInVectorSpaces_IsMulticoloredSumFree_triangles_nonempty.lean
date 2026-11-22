-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_triangles_nonempty
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.triangles_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:19.700836+00:00
-- url     : https://prove2.me/theorems/19ca809a-8163-4669-aed0-1fde5fe75477
-- title:
--   Is Multicolored Sum Free: triangles nonempty
-- statement:
--   Removing fewer than `m * #W` elements from the sets `X × W`, `Y × W` and `Z × W` built from a
--   multicolored sum-free family of `m` triples leaves a triangle.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L171-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L171-L187

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

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.triangles_nonempty (h : IsMulticoloredSumFree x y z)
    {X Y Z : Finset (G × W)}
    (hcard : #((univ.image x ×ˢ univ) \ X) + #((univ.image y ×ˢ univ) \ Y) +
      #((univ.image z ×ˢ univ) \ Z) < Fintype.card ι * Fintype.card W) :
    (triangles X Y Z).Nonempty := by sorry
