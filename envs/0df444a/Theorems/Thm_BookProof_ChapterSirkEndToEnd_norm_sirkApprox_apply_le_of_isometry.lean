-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_norm_sirkApprox_apply_le_of_isometry
-- name    : BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le_of_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:10:35.344172+00:00
-- url     : https://prove2.me/theorems/744a211a-d568-47f6-b492-3ea0e47ba2ec
-- title:
--   (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (hpsi : ∀ y : F, ‖psiB y‖ = ‖y‖) (v : E) : ‖sirkApprox V psiB v‖ ≤ ‖v‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le_of_isometry` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le_of_isometry
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le_of_isometry (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hpsi : ∀ y : F, ‖psiB y‖ = ‖y‖) (v : E) :
    ‖sirkApprox V psiB v‖ ≤ ‖v‖ := by sorry
