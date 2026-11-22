-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_sum_range_succ_cast
-- name    : ArithmeticTriangleRemovalInVectorSpaces.sum_range_succ_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:59.918837+00:00
-- url     : https://prove2.me/theorems/3e1e5063-744f-4d33-baef-c79a3b3c6902
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: sum range succ cast
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the sum range succ cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L95-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L95-L101

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

theorem ArithmeticTriangleRemovalInVectorSpaces.sum_range_succ_cast (k : ℕ) : ∑ j ∈ range (k + 1), (j : ℝ) = k * (k + 1) / 2 := by sorry
