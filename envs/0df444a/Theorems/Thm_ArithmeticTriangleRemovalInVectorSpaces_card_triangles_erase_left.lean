-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_erase_left
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_triangles_erase_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:52.963428+00:00
-- url     : https://prove2.me/theorems/bab934ed-130b-468f-a298-aeefa6585661
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card triangles erase left
-- statement:
--   Removing a vertex `v` from `X` removes the triangles whose first vertex is `v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Triangle/Basic.lean#L70-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Triangle/Basic.lean#L70-L77

module
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {X Y Z X' Y' Z' : Finset G} {x y z : G}

theorem ArithmeticTriangleRemovalInVectorSpaces.card_triangles_erase_left (X Y Z : Finset G) (v : G) :
    #(triangles (X.erase v) Y Z) + #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) =
      #(triangles X Y Z) := by sorry
