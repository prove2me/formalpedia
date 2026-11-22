-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mass_smul
-- name    : ArithmeticTriangleRemovalInVectorSpaces.mass_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:57.754177+00:00
-- url     : https://prove2.me/theorems/96e44c31-e85d-4773-ab54-f20318a3c1c0
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: mass smul
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the mass smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L71-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L71-L72

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

theorem ArithmeticTriangleRemovalInVectorSpaces.mass_smul (r : ℝ) : mass N (r • π) = r * mass N π := by sorry
