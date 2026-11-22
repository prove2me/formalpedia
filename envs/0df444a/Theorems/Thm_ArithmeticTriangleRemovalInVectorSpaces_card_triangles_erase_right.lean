-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_erase_right
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_triangles_erase_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:50.684807+00:00
-- url     : https://prove2.me/theorems/2353cb96-8bea-462f-80cb-c5d79c6c514e
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card triangles erase right
-- statement:
--   Removing a vertex `v` from `Z` removes the triangles whose third vertex is `v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Triangle/Basic.lean#L90-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Triangle/Basic.lean#L90-L97

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

theorem ArithmeticTriangleRemovalInVectorSpaces.card_triangles_erase_right (X Y Z : Finset G) (v : G) :
    #(triangles X Y (Z.erase v)) + #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) =
      #(triangles X Y Z) := by sorry
