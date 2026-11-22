-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_weight_nonneg
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.weight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:55.372752+00:00
-- url     : https://prove2.me/theorems/e218a14d-4c25-490a-b1a0-3f5068a98de7
-- title:
--   Is Decreasing On: weight nonneg
-- statement:
--   The Is Decreasing On construction uses the weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L191-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L191-L194

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

theorem ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.weight_nonneg (h : IsDecreasingOn N π) (k : ℕ) :
    0 ≤ (k + 1 : ℝ) * (π k - π (k + 1)) := by sorry
