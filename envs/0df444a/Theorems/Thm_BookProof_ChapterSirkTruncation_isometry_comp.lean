-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTruncation_isometry_comp
-- name    : BookProof.ChapterSirkTruncation.isometry_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:37:08.085872+00:00
-- url     : https://prove2.me/theorems/110fa80e-bc57-4d75-8665-83d45ae7417b
-- title:
--   (V : F →L[ℂ] E) (W : G →L[ℂ] F) (hV : ∀ x : F, ‖V x‖ = ‖x‖) (hW : ∀ x : G, ‖W x‖ = ‖x‖) (x : G) : ‖(V.comp W) x‖ = ‖x‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTruncation.isometry_comp` (module `BookProof.ChapterSirkTruncation`), source chapter `BookProof/ChapterChapterSirkTruncation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTruncation.lean

-- Generated from ChapterSirkTruncation.lean — theorem BookProof.ChapterSirkTruncation.isometry_comp
import Mathlib
import Definitions.Def_ChapterSirkTruncation
open BookProof.ChapterSirkTruncation








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkWhitening

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in

theorem BookProof.ChapterSirkTruncation.isometry_comp (V : F →L[ℂ] E) (W : G →L[ℂ] F)
    (hV : ∀ x : F, ‖V x‖ = ‖x‖) (hW : ∀ x : G, ‖W x‖ = ‖x‖) (x : G) :
    ‖(V.comp W) x‖ = ‖x‖ := by sorry
