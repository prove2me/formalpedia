-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_isReducingProjection_asymProj
-- name    : BookProof.ReducedEsa.isReducingProjection_asymProj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:31:52.507887+00:00
-- url     : https://prove2.me/theorems/b1326f24-c0d0-47d8-bc90-44f18009b693
-- title:
--   `BookProof.ReducedEsa.isReducingProjection_asymProj` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) : IsReducingProjection (asymProj U) where i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.isReducingProjection_asymProj` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) : IsReducingProjection (asymProj U) where idem x
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.isReducingProjection_asymProj`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.isReducingProjection_asymProj
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

theorem BookProof.ReducedEsa.isReducingProjection_asymProj (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) :
    IsReducingProjection (asymProj U) := by sorry
