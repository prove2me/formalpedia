-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_symProj_mem
-- name    : BookProof.ReducedEsa.symProj_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:31:58.201015+00:00
-- url     : https://prove2.me/theorems/2129723c-6e19-4788-9a32-dbbf2b743761
-- title:
--   `BookProof.ReducedEsa.symProj_mem` (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, symProj U x ∈ D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.symProj_mem` (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, symProj U x ∈ D
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.symProj_mem`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.symProj_mem
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
open BookProof.ReducedEsa



open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {P : F →ₗ[ℂ] F}
variable {D : Submodule ℂ F}
variable (T : D →ₗ[ℂ] F)
variable {T}
variable (U : F →ₗ[ℂ] F)
variable {U}

theorem BookProof.ReducedEsa.symProj_mem (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, symProj U x ∈ D := by sorry
