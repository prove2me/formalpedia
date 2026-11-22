-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_rpow_le_rpow_sub
-- name    : ArithmeticTriangleRemovalInVectorSpaces.mul_rpow_le_rpow_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:35.436472+00:00
-- url     : https://prove2.me/theorems/5e8a7b4d-2a6a-429b-8f94-26657e857572
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: mul rpow le rpow sub
-- statement:
--   For `A > 0` and `0 < ε ≤ A⁻¹ ^ (2 / η)` with `ε ≤ 1`, lowering the exponent from `1 + κ` to
--   `C - η`, where `C - η / 2 ≤ 1 + κ`, absorbs the factor `A`: `A * ε ^ (1 + κ) ≤ ε ^ (C - η)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L87-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L87-L98

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.mul_rpow_le_rpow_sub {A ε κ C η : ℝ} (hA : 0 < A) (hε0 : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 < η)
    (hκ : C - η / 2 ≤ 1 + κ) (hε : ε ≤ A⁻¹ ^ (2 / η)) : A * ε ^ (1 + κ) ≤ ε ^ (C - η) := by sorry
