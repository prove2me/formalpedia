-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_inv_pow_le_inv_add_sq_rpow
-- name    : ArithmeticTriangleRemovalInVectorSpaces.inv_pow_le_inv_add_sq_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:33.5108+00:00
-- url     : https://prove2.me/theorems/dcc63e43-b054-464b-ac3d-f7148095736b
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: inv pow le inv add sq rpow
-- statement:
--   For `P ≥ 2`, `η > 0` and `6 / η ≤ n`, `(P ^ n)⁻¹ ≤ (P + P ^ 2)⁻¹ ^ (2 / η)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L101-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L101-L108

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.inv_pow_le_inv_add_sq_rpow {P η : ℝ} (hP : 2 ≤ P) (hη : 0 < η) {n : ℕ} (hn : 6 / η ≤ n) :
    (P ^ n)⁻¹ ≤ (P + P ^ 2)⁻¹ ^ (2 / η) := by sorry
