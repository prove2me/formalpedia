-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_map
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:50.198858+00:00
-- url     : https://prove2.me/theorems/96adb5df-9442-4f66-8006-1292bffeb85e
-- title:
--   Is Multicolored Sum Free: map
-- statement:
--   The image of a multicolored sum-free family under an injective additive map is multicolored
--   sum-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Basic.lean#L56-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Basic.lean#L56-L60

module
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
variable {ι G H : Type*} [AddCommGroup G] [AddCommGroup H]
open ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree
variable {x y z : ι → G}

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.map (h : IsMulticoloredSumFree x y z) (e : G →+ H) (he : Function.Injective e) :
    IsMulticoloredSumFree (e ∘ x) (e ∘ y) (e ∘ z) := by sorry
