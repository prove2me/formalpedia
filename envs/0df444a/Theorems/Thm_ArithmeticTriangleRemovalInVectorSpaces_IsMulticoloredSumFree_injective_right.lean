-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_right
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.injective_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:07.611875+00:00
-- url     : https://prove2.me/theorems/710a7123-63a6-4cef-a85f-9f96ef202e86
-- title:
--   Is Multicolored Sum Free: injective right
-- statement:
--   The third vertices of a multicolored sum-free family are distinct.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L57-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L57-L60

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

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.injective_right (h : IsMulticoloredSumFree x y z) : Injective z := by sorry
