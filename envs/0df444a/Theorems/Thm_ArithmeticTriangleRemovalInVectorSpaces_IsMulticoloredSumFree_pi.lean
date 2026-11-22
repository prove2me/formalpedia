-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_pi
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:48.165877+00:00
-- url     : https://prove2.me/theorems/d5ef3e78-3fbe-41a6-91ee-13d2d153132b
-- title:
--   Is Multicolored Sum Free: pi
-- statement:
--   The coordinatewise power of a multicolored sum-free family is multicolored sum-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Basic.lean#L48-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Basic.lean#L48-L52

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

theorem ArithmeticTriangleRemovalInVectorSpaces.IsMulticoloredSumFree.pi (h : IsMulticoloredSumFree x y z) (κ : Type*) :
    IsMulticoloredSumFree (fun (I : κ → ι) t ↦ x (I t)) (fun I t ↦ y (I t)) fun I t ↦ z (I t) := by sorry
