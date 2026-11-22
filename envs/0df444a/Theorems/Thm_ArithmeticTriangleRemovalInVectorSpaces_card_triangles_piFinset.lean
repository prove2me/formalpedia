-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_piFinset
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_triangles_piFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:03.468454+00:00
-- url     : https://prove2.me/theorems/f5d89c54-59d1-4fbf-99c4-341e264ebe96
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card triangles pi Finset
-- statement:
--   The triangles of the coordinatewise powers `X ^ k`, `Y ^ k` and `Z ^ k` are the `k`-tuples of
--   triangles of `X × Y × Z`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Triangle/Basic.lean#L101-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Triangle/Basic.lean#L101-L108

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

theorem ArithmeticTriangleRemovalInVectorSpaces.card_triangles_piFinset (X Y Z : Finset G) (k : ℕ) :
    #(triangles (Fintype.piFinset fun _ : Fin k ↦ X) (Fintype.piFinset fun _ ↦ Y)
      (Fintype.piFinset fun _ ↦ Z)) = #(triangles X Y Z) ^ k := by sorry
