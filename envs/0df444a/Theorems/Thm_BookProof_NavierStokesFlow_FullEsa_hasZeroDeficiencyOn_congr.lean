-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_hasZeroDeficiencyOn_congr
-- name    : BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_congr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T12:02:49.09468+00:00
-- url     : https://prove2.me/theorems/b7ab2957-a155-454f-844f-3d5d09492379
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_congr` {D : Submodule ℂ F} {H₁ H₂ : D →ₗ[ℂ] D} (h : ∀ x : D, (H₁ x : F) = (H₂ x : F)) (h₁ : HasZeroDeficiencyOn D H₁)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_congr` {D : Submodule ℂ F} {H₁ H₂ : D →ₗ[ℂ] D} (h : ∀ x : D, (H₁ x : F) = (H₂ x : F)) (h₁ : HasZeroDeficiencyOn D H₁) : HasZeroDeficiencyOn D H₂
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_congr`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_congr
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_congr {D : Submodule ℂ F} {H₁ H₂ : D →ₗ[ℂ] D}
    (h : ∀ x : D, (H₁ x : F) = (H₂ x : F)) (h₁ : HasZeroDeficiencyOn D H₁) :
    HasZeroDeficiencyOn D H₂ := by sorry
