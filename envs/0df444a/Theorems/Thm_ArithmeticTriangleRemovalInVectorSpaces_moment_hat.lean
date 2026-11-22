-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_moment_hat
-- name    : ArithmeticTriangleRemovalInVectorSpaces.moment_hat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:50.344799+00:00
-- url     : https://prove2.me/theorems/304cc447-336b-4319-bcb1-7db5c30c17f5
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: moment hat
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the moment hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L160-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L160-L168

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

theorem ArithmeticTriangleRemovalInVectorSpaces.moment_hat (w : ℕ → ℝ) :
    moment N (hat N w) = (∑ k ∈ range (N + 1), (k : ℝ) * w k) / 2 := by sorry
