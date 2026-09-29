-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_norm_sirkApprox_apply_le
-- name    : BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:09:57.990593+00:00
-- url     : https://prove2.me/theorems/ecb29f43-8cf8-473c-92f9-f1de8b13a3b3
-- title:
--   (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (v : E) : ‖sirkApprox V psiB v‖ ≤ ‖psiB‖ * ‖v‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (v : E) :
    ‖sirkApprox V psiB v‖ ≤ ‖psiB‖ * ‖v‖ := by sorry
