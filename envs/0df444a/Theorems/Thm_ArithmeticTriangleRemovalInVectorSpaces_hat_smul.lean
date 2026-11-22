-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_hat_smul
-- name    : ArithmeticTriangleRemovalInVectorSpaces.hat_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:34.900411+00:00
-- url     : https://prove2.me/theorems/3b73573e-ebcc-4494-8d5b-7aff02e39738
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: hat smul
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the hat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L141-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L141-L143

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

theorem ArithmeticTriangleRemovalInVectorSpaces.hat_smul (r : ℝ) (w : ℕ → ℝ) : hat N (r • w) = r • hat N w := by sorry
