-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_farisLavine_holds_of_everywhereDefined
-- name    : BookProof.NavierStokesFlow.farisLavine_holds_of_everywhereDefined
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:23:38.941766+00:00
-- url     : https://prove2.me/theorems/5fedf756-3208-438f-bc4e-e570c36ab8d8
-- title:
--   The Lean 4 theorem `farisLavine_holds_of_everywhereDefined` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `farisLavine_holds_of_everywhereDefined` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.farisLavine_holds_of_everywhereDefined
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.farisLavine_holds_of_everywhereDefined :
    ∀ (H' N' : F →ₗ[ℂ] F) (a b : ℝ), H'.IsSymmetric →
      (∀ v : F, ‖H' v‖ ≤ a * ‖N' v‖) →
      (∀ v : F, ‖(inner ℂ v (H' (N' v) - N' (H' v)) : ℂ)‖ ≤ b * ‖(inner ℂ v (N' v) : ℂ)‖) →
      HasZeroDeficiency H' := by sorry
