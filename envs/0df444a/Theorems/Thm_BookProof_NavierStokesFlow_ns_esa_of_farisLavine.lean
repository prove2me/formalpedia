-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ns_esa_of_farisLavine
-- name    : BookProof.NavierStokesFlow.ns_esa_of_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:19.446256+00:00
-- url     : https://prove2.me/theorems/072f4cd3-339e-49c8-bff3-876506662520
-- title:
--   The Lean 4 theorem `ns_esa_of_farisLavine` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ns_esa_of_farisLavine` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.ns_esa_of_farisLavine
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.ns_esa_of_farisLavine (H N : F →ₗ[ℂ] F) (c₁ c₂ : ℝ) (hsym : H.IsSymmetric)
    (farisLavine : ∀ (H' N' : F →ₗ[ℂ] F) (a b : ℝ), H'.IsSymmetric →
      (∀ v : F, ‖H' v‖ ≤ a * ‖N' v‖) →
      (∀ v : F, ‖(inner ℂ v (H' (N' v) - N' (H' v)) : ℂ)‖ ≤ b * ‖(inner ℂ v (N' v) : ℂ)‖) →
      HasZeroDeficiency H')
    (hHbound : ∀ v : F, ‖H v‖ ≤ c₁ * ‖N v‖)
    (hCommutator : ∀ v : F,
      ‖(inner ℂ v (H (N v) - N (H v)) : ℂ)‖ ≤ c₂ * ‖(inner ℂ v (N v) : ℂ)‖) :
    HasZeroDeficiency H := by sorry
