-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_eq_zero_of_lt
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.eq_zero_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:31.659495+00:00
-- url     : https://prove2.me/theorems/0059988c-b78d-4dae-83e3-e7205708d4b7
-- title:
--   Is Decreasing On: eq zero of lt
-- statement:
--   The Is Decreasing On construction uses the eq zero of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L114-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L114-L116

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}

theorem ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.eq_zero_of_lt (h : IsDecreasingOn N π) {k : ℕ} (hk : N < k) : π k = 0 := by sorry
