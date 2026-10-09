-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_isReducingProjection_symProj
-- name    : BookProof.ReducedEsa.isReducingProjection_symProj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:31:43.879822+00:00
-- url     : https://prove2.me/theorems/f0555c0e-718f-41b6-b82d-38d079c29846
-- title:
--   `BookProof.ReducedEsa.isReducingProjection_symProj` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) : IsReducingProjection (symProj U) where ide
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.isReducingProjection_symProj` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) : IsReducingProjection (symProj U) where idem x
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.isReducingProjection_symProj`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.isReducingProjection_symProj
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

theorem BookProof.ReducedEsa.isReducingProjection_symProj (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) :
    IsReducingProjection (symProj U) := by sorry
