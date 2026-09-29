-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirkApprox_apply
-- name    : BookProof.ChapterSirkEndToEnd.sirkApprox_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:45:26.734946+00:00
-- url     : https://prove2.me/theorems/01485dc3-09ff-4c02-ae93-c79a9fee8a32
-- title:
--   (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (v : E) : sirkApprox V psiB v = V (psiB (V.adjoint v))
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.sirkApprox_apply` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.sirkApprox_apply
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.sirkApprox_apply (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (v : E) :
    sirkApprox V psiB v = V (psiB (V.adjoint v)) := by sorry
