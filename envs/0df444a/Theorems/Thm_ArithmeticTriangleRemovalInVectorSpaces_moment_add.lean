-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_add
-- name    : ArithmeticTriangleRemovalInVectorSpaces.moment_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:01.250878+00:00
-- url     : https://prove2.me/theorems/3b452aed-f961-4c1d-9e18-fa8fcdd71849
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: moment add
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the moment add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L74-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L74-L75

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

theorem ArithmeticTriangleRemovalInVectorSpaces.moment_add : moment N (π + π') = moment N π + moment N π' := by sorry
