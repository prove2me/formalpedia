-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_smul
-- name    : ArithmeticTriangleRemovalInVectorSpaces.moment_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:59.23259+00:00
-- url     : https://prove2.me/theorems/3b01b585-8211-49a4-aa35-57a5f50c8b33
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: moment smul
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the moment smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L80-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L80-L83

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

theorem ArithmeticTriangleRemovalInVectorSpaces.moment_smul (r : ℝ) : moment N (r • π) = r * moment N π := by sorry
