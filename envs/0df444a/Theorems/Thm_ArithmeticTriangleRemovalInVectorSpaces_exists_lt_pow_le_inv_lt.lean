-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_lt_pow_le_inv_lt
-- name    : ArithmeticTriangleRemovalInVectorSpaces.exists_lt_pow_le_inv_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:27.632797+00:00
-- url     : https://prove2.me/theorems/6c92ad2c-9707-4334-94f1-177f87dda0fa
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: exists lt pow le inv lt
-- statement:
--   For `t > 1` and `0 < ε < t ^ (-(n₀ + 1))` there is `n > n₀` with `t ^ n ≤ ε⁻¹ < t ^ (n + 1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L40-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L40-L44

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.exists_lt_pow_le_inv_lt {t ε : ℝ} (ht : 1 < t) {n₀ : ℕ} (hε0 : 0 < ε)
    (hε : ε < (t ^ (n₀ + 1))⁻¹) : ∃ n, n₀ < n ∧ t ^ n ≤ ε⁻¹ ∧ ε⁻¹ < t ^ (n + 1) := by sorry
