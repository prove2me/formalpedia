-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_compatible_hat
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsBalanced.compatible_hat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:58.218802+00:00
-- url     : https://prove2.me/theorems/839be709-a255-4adf-a9dc-3bbbd9beb628
-- title:
--   Is Balanced: compatible hat
-- statement:
--   **Lemma 2.1 of Pebody, after applying `hat`.** The `hat` of a balanced triple of weights is
--   compatible, given Pebody's theorem at lower levels.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Decomposition.lean#L305-L307
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Decomposition.lean#L305-L307

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {w w₁ w₂ w₃ σ σ₁ σ₂ σ₃ : ℕ → ℝ} {μ μ₁ μ₂ μ₃ p : ℝ}

theorem ArithmeticTriangleRemovalInVectorSpaces.IsBalanced.compatible_hat (ih : ∀ m < N, DecreasingCompatible m)
    (hb : IsBalanced N w₁ w₂ w₃) : Compatible N (hat N w₁) (hat N w₂) (hat N w₃) := by sorry
