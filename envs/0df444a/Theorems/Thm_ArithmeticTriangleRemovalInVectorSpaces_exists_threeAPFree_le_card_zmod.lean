-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_threeAPFree_le_card_zmod
-- name    : ArithmeticTriangleRemovalInVectorSpaces.exists_threeAPFree_le_card_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:06.858916+00:00
-- url     : https://prove2.me/theorems/147ec6e5-4b9b-4782-b7d8-3cfd8dd58ae0
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: exists three APFree le card zmod
-- statement:
--   **Behrend's construction in `ZMod P`.** There is a set `S` in `ZMod P` without three-term
--   arithmetic progressions and with at least `P / 2 * exp (-4 * √(log P))` elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Behrend.lean#L33-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Behrend.lean#L33-L49

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Combinatorics.Additive.AP.Three.Behrend
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Behrend
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.exists_threeAPFree_le_card_zmod {P : ℕ} (hP : 0 < P) :
    ∃ S : Finset (ZMod P), ThreeAPFree (S : Set (ZMod P)) ∧ P / 2 * exp (-4 * √(log P)) ≤ #S := by sorry
