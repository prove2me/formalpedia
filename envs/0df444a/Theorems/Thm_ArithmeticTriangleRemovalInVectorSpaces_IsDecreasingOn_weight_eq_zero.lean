-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_weight_eq_zero
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.weight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:57.38065+00:00
-- url     : https://prove2.me/theorems/07810de9-392f-4d1b-b1b7-5c71f38691aa
-- title:
--   Is Decreasing On: weight eq zero
-- statement:
--   The Is Decreasing On construction uses the weight eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L196-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L196-L198

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}

theorem ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.weight_eq_zero (h : IsDecreasingOn N π) {k : ℕ} (hk : N < k) :
    (k + 1 : ℝ) * (π k - π (k + 1)) = 0 := by sorry
