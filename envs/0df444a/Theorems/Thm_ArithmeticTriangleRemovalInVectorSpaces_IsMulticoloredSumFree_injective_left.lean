-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_injective_left
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.injective_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:17.466256+00:00
-- url     : https://prove2.me/theorems/043b537e-292f-4711-956d-27a2a065668b
-- title:
--   Is Multicolored Sum Free: injective left
-- statement:
--   The first vertices of a multicolored sum-free family are distinct.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L45-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Product.lean#L45-L48

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

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.injective_left (h : IsMulticoloredSumFree x y z) : Injective x := by sorry
