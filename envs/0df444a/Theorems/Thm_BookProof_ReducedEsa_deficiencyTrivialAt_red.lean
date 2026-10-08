-- Prove2me | Theorems.Thm_BookProof_ReducedEsa_deficiencyTrivialAt_red
-- name    : BookProof.ReducedEsa.deficiencyTrivialAt_red
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:31:05.840855+00:00
-- url     : https://prove2.me/theorems/f0322682-9d38-4251-8e90-b7f7fc010a09
-- title:
--   `BookProof.ReducedEsa.deficiencyTrivialAt_red` (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D} (hC : Commutes T hPD) {z : ℂ} (hz : DeficiencyTrivialAt D T z) : DeficiencyTri
-- statement:
--   Prove the following Lean 4 theorem from `ChapterReducingSubspaceEsa`.
--
--   `BookProof.ReducedEsa.deficiencyTrivialAt_red` (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D} (hC : Commutes T hPD) {z : ℂ} (hz : DeficiencyTrivialAt D T z) : DeficiencyTrivialAt (redDom P D) (redOp T hP hC) z
--
--   Formalization note: Lean 4 identifier `BookProof.ReducedEsa.deficiencyTrivialAt_red`.

-- Generated from ChapterReducingSubspaceEsa.lean — theorem BookProof.ReducedEsa.deficiencyTrivialAt_red
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

theorem BookProof.ReducedEsa.deficiencyTrivialAt_red (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) {z : ℂ} (hz : DeficiencyTrivialAt D T z) :
    DeficiencyTrivialAt (redDom P D) (redOp T hP hC) z := by sorry
