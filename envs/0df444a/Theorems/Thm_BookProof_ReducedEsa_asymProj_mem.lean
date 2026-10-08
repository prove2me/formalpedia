-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_asymProj_mem
-- name    : BookProof.ReducedEsa.asymProj_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:32:23.562781+00:00
-- url     : https://prove2.me/theorems/5a0de051-a709-42bb-920a-47ad9a2d3afa
-- title:
--   `BookProof.ReducedEsa.asymProj_mem` (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, asymProj U x ∈ D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.asymProj_mem` (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, asymProj U x ∈ D
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.asymProj_mem`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.asymProj_mem
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

theorem BookProof.ReducedEsa.asymProj_mem (hUD : ∀ x ∈ D, U x ∈ D) : ∀ x ∈ D, asymProj U x ∈ D := by sorry
