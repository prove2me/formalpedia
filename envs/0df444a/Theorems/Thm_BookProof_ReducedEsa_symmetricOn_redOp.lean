-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_symmetricOn_redOp
-- name    : BookProof.ReducedEsa.symmetricOn_redOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:30:58.811143+00:00
-- url     : https://prove2.me/theorems/f5f41a06-3ded-4c33-89fa-2a67d0fb5bd6
-- title:
--   `BookProof.ReducedEsa.symmetricOn_redOp` (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D} (hC : Commutes T hPD) (hT : SymmetricOn D T) : SymmetricOn (redDom P D) (redOp T hP
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.symmetricOn_redOp` (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D} (hC : Commutes T hPD) (hT : SymmetricOn D T) : SymmetricOn (redDom P D) (redOp T hP hC)
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.symmetricOn_redOp`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.symmetricOn_redOp
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

theorem BookProof.ReducedEsa.symmetricOn_redOp (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) (hT : SymmetricOn D T) :
    SymmetricOn (redDom P D) (redOp T hP hC) := by sorry
