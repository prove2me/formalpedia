-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_red
-- name    : BookProof.ReducedEsa.essentiallySelfAdjointOn_red
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:31:54.018321+00:00
-- url     : https://prove2.me/theorems/509e7820-3d4a-4a13-b3b1-1b04e740b27f
-- title:
--   `BookProof.ReducedEsa.essentiallySelfAdjointOn_red` (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D} (hC : Commutes T hPD) (hesa : EssentiallySelfAdjointOn D T) : Essentially
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.essentiallySelfAdjointOn_red` (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D} (hC : Commutes T hPD) (hesa : EssentiallySelfAdjointOn D T) : EssentiallySelfAdjointOn (redDom P D) (redOp T hP hC)
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.essentiallySelfAdjointOn_red`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.essentiallySelfAdjointOn_red
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterA
import Definitions.Def_ChapterFarisLavineCore
open BookProof.ChapterA
open BookProof.ChapterA.System
open BookProof.ReducedEsa



open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {P : F →ₗ[ℂ] F}
variable {D : Submodule ℂ F}
variable (T : D →ₗ[ℂ] F)
variable {T}

theorem BookProof.ReducedEsa.essentiallySelfAdjointOn_red (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) (hesa : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (redDom P D) (redOp T hP hC) := by sorry
