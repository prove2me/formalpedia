-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_mul_rpow_one_add_of_mul_sq_le
-- name    : ArithmeticTriangleRemovalInVectorSpaces.le_mul_rpow_one_add_of_mul_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:32.3098+00:00
-- url     : https://prove2.me/theorems/45941aa7-f092-4817-a4e8-0195b62ec176
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: le mul rpow one add of mul sq le
-- statement:
--   If `δ * N ^ 2 ≤ ε * N + 1` and `N⁻¹ ≤ P * ε ^ κ` with `κ ≥ 1` and `0 < ε ≤ 1`, then
--   `δ ≤ (P + P ^ 2) * ε ^ (1 + κ)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L72-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Tightness/Exponent.lean#L72-L83

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.le_mul_rpow_one_add_of_mul_sq_le {P N ε δ κ : ℝ} (hP : 0 < P) (hN : 0 < N) (hε0 : 0 < ε)
    (hε₁ : ε ≤ 1) (hκ : 1 ≤ κ) (hNε : N⁻¹ ≤ P * ε ^ κ) (hδ : δ * N ^ 2 ≤ ε * N + 1) :
    δ ≤ (P + P ^ 2) * ε ^ (1 + κ) := by sorry
