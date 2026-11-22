-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_comp
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:48.206867+00:00
-- url     : https://prove2.me/theorems/2cffd926-f9d4-4b1d-a9bf-9adced0b9bec
-- title:
--   Is Multicolored Sum Free: comp
-- statement:
--   A subfamily of a multicolored sum-free family, indexed through an injective map, is
--   multicolored sum-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Basic.lean#L64-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Basic.lean#L64-L67

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

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.comp {κ : Type*} (h : IsMulticoloredSumFree x y z) {f : κ → ι} (hf : Function.Injective f) :
    IsMulticoloredSumFree (x ∘ f) (y ∘ f) (z ∘ f) := by sorry
