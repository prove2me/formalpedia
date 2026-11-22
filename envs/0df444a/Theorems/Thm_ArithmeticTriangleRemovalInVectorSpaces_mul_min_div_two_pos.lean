-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_min_div_two_pos
-- name    : ArithmeticTriangleRemovalInVectorSpaces.mul_min_div_two_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:23.089979+00:00
-- url     : https://prove2.me/theorems/69e04f66-f158-4b99-bd10-ee2673f1b086
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: mul min div two pos
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the mul min div two pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L115-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L115-L118

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.mul_min_div_two_pos {c η : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) (hη : 0 < η) :
    0 < c * min (1 - c) (c * η / 2) / 2 := by sorry
