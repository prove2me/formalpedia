-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_symmetric_of_involutive_isometry
-- name    : BookProof.ReducedEsa.symmetric_of_involutive_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:31:34.530661+00:00
-- url     : https://prove2.me/theorems/d6774d17-6725-4984-a193-3b2392b808e5
-- title:
--   `BookProof.ReducedEsa.symmetric_of_involutive_isometry` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) (x y : F) : (inner ℂ (U x) y : ℂ) = inne
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.symmetric_of_involutive_isometry` (hU2 : ∀ x, U (U x) = x) (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) (x y : F) : (inner ℂ (U x) y : ℂ) = inner ℂ x (U y)
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.symmetric_of_involutive_isometry`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.symmetric_of_involutive_isometry
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

theorem BookProof.ReducedEsa.symmetric_of_involutive_isometry (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) (x y : F) :
    (inner ℂ (U x) y : ℂ) = inner ℂ x (U y) := by sorry
