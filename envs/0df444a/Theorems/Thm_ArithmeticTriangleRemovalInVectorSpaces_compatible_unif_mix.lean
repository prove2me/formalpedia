-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_compatible_unif_mix
-- name    : ArithmeticTriangleRemovalInVectorSpaces.compatible_unif_mix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:00.184856+00:00
-- url     : https://prove2.me/theorems/30dd84b1-215a-4bd2-92d5-0302ce695f7b
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: compatible unif mix
-- statement:
--   `unif k₁`, `unif k₂` and `α • unif y + (1 - α) • unif z` are compatible at level `N` when their
--   means sum to `N`, given Pebody's theorem at lower levels.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L299-L332
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L299-L332

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

theorem ArithmeticTriangleRemovalInVectorSpaces.compatible_unif_mix (ih : ∀ m < N, DecreasingCompatible m) {k₁ k₂ y z : ℕ} (hk₁ : k₁ ≤ N)
    (hk₂ : k₂ ≤ N) (hy : y ≤ N) (hz : z ≤ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hsum : (k₁ + k₂ + α * y + (1 - α) * z : ℝ) = 2 * N) :
    Compatible N (unif k₁) (unif k₂) (α • unif y + (1 - α) • unif z) := by sorry
