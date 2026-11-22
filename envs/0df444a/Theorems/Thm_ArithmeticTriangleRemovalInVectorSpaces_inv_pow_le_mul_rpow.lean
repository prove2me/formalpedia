-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_inv_pow_le_mul_rpow
-- name    : ArithmeticTriangleRemovalInVectorSpaces.inv_pow_le_mul_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:26.04818+00:00
-- url     : https://prove2.me/theorems/a531558b-32c0-41de-a8e9-b54de6bf8aa7
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: inv pow le mul rpow
-- statement:
--   If `ε⁻¹ < (P ^ κ⁻¹) ^ (n + 1)` with `P, ε, κ > 0`, then `(P ^ n)⁻¹ ≤ P * ε ^ κ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L61-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L61-L68

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.inv_pow_le_mul_rpow {P ε κ : ℝ} {n : ℕ} (hP : 0 < P) (hε : 0 < ε) (hκ : 0 < κ)
    (h : ε⁻¹ < (P ^ κ⁻¹) ^ (n + 1)) : (P ^ n)⁻¹ ≤ P * ε ^ κ := by sorry
