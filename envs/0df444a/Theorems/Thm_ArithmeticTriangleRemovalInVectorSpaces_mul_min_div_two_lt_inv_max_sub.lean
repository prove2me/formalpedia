-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_min_div_two_lt_inv_max_sub
-- name    : ArithmeticTriangleRemovalInVectorSpaces.mul_min_div_two_lt_inv_max_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:36.078118+00:00
-- url     : https://prove2.me/theorems/ec13fddd-9602-43ed-9846-6ec44844bc3c
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: mul min div two lt inv max sub
-- statement:
--   For `0 < c < 1` and `η > 0`, the exponent `η' = c * min (1 - c) (c * η / 2) / 2` satisfies
--   `η' < 1 / κ - c` for `κ = max 1 (1 / c - η / 2)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L122-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L122-L131

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.mul_min_div_two_lt_inv_max_sub {c η : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) (hη : 0 < η) :
    c * min (1 - c) (c * η / 2) / 2 < (max 1 (c⁻¹ - η / 2))⁻¹ - c := by sorry
