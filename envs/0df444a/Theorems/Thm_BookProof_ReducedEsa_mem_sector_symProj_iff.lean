-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_mem_sector_symProj_iff
-- name    : BookProof.ReducedEsa.mem_sector_symProj_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:32:27.468004+00:00
-- url     : https://prove2.me/theorems/a42e5b54-9c0a-4a94-a73f-2bbab14057ca
-- title:
--   `BookProof.ReducedEsa.mem_sector_symProj_iff` (hU2 : ∀ x, U (U x) = x) {x : F} : x ∈ sector (symProj U) ↔ U x = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.mem_sector_symProj_iff` (hU2 : ∀ x, U (U x) = x) {x : F} : x ∈ sector (symProj U) ↔ U x = x
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.mem_sector_symProj_iff`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.mem_sector_symProj_iff
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

theorem BookProof.ReducedEsa.mem_sector_symProj_iff (hU2 : ∀ x, U (U x) = x) {x : F} :
    x ∈ sector (symProj U) ↔ U x = x := by sorry
