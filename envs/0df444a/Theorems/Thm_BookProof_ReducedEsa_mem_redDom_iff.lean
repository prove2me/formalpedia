-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_mem_redDom_iff
-- name    : BookProof.ReducedEsa.mem_redDom_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:31:00.853168+00:00
-- url     : https://prove2.me/theorems/7acc51f0-6938-4b4d-a3f4-5ebf2d499309
-- title:
--   `BookProof.ReducedEsa.mem_redDom_iff` {x : sector P} : x ∈ redDom P D ↔ (x : F) ∈ D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.mem_redDom_iff` {x : sector P} : x ∈ redDom P D ↔ (x : F) ∈ D
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.mem_redDom_iff`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.mem_redDom_iff
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

theorem BookProof.ReducedEsa.mem_redDom_iff {x : sector P} : x ∈ redDom P D ↔ (x : F) ∈ D := by sorry
