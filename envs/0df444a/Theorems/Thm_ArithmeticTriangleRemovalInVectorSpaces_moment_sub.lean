-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_sub
-- name    : ArithmeticTriangleRemovalInVectorSpaces.moment_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:56.31498+00:00
-- url     : https://prove2.me/theorems/1625383d-deac-49c5-aeb9-a06788cb769a
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: moment sub
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the moment sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L77-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L77-L78

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

theorem ArithmeticTriangleRemovalInVectorSpaces.moment_sub : moment N (π - π') = moment N π - moment N π' := by sorry
