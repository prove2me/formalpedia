-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_div_le_sq_div_mul_min_div_two
-- name    : ArithmeticTriangleRemovalInVectorSpaces.div_le_sq_div_mul_min_div_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:35.77763+00:00
-- url     : https://prove2.me/theorems/4e29518b-e172-4313-b83a-a2dbfe277b81
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: div le sq div mul min div two
-- statement:
--   For `0 < c < 1`, `η > 0` and `X ≥ 1`, the exponent `η' = c * min (1 - c) (c * η / 2) / 2`
--   satisfies `6 / η ≤ (X / η') ^ 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L135-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L135-L145

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.div_le_sq_div_mul_min_div_two {c η X : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) (hη : 0 < η)
    (hX : 1 ≤ X) : 6 / η ≤ (X / (c * min (1 - c) (c * η / 2) / 2)) ^ 2 := by sorry
