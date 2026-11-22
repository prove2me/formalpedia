-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mass_sub
-- name    : ArithmeticTriangleRemovalInVectorSpaces.mass_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:57.292117+00:00
-- url     : https://prove2.me/theorems/117083b5-0c71-4940-9640-d26b15f2d323
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: mass sub
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the mass sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L68-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L68-L69

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

theorem ArithmeticTriangleRemovalInVectorSpaces.mass_sub : mass N (π - π') = mass N π - mass N π' := by sorry
