-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mul_pow_lt_of_rpow_mul_le
-- name    : ArithmeticTriangleRemovalInVectorSpaces.mul_pow_lt_of_rpow_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:26.606809+00:00
-- url     : https://prove2.me/theorems/14af29f1-b2dc-4783-a399-c2145fe3e32b
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: mul pow lt of rpow mul le
-- statement:
--   If `(P ^ γ) ^ n ≤ ε⁻¹` and `P ^ (a * n) ≤ m` with `1 - γ < a`, `P > 1` and `n > 0`, then
--   `ε * P ^ n < m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L48-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L48-L58

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.mul_pow_lt_of_rpow_mul_le {P ε γ a m : ℝ} {n : ℕ} (hP : 1 < P) (hε : 0 < ε) (hn : 0 < n)
    (ha : 1 - γ < a) (h : (P ^ γ) ^ n ≤ ε⁻¹) (hm : P ^ (a * n) ≤ m) : ε * P ^ n < m := by sorry
