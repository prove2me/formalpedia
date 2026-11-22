-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_middle
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.injective_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:10.812815+00:00
-- url     : https://prove2.me/theorems/456135dc-7332-4fae-ac20-ee1db21b00b5
-- title:
--   Is Multicolored Sum Free: injective middle
-- statement:
--   The second vertices of a multicolored sum-free family are distinct.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L51-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L51-L54

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

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.injective_middle (h : IsMulticoloredSumFree x y z) : Injective y := by sorry
