-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTruncation_adjoint_reconstruction_eq
-- name    : BookProof.ChapterSirkTruncation.adjoint_reconstruction_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:35:39.017071+00:00
-- url     : https://prove2.me/theorems/69169c70-64e0-482c-bb6d-4a5a919f7e14
-- title:
--   (V : F →L[ℂ] E) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (v : E) : V.adjoint (V (V.adjoint v)) = V.adjoint v
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTruncation.adjoint_reconstruction_eq` (module `BookProof.ChapterSirkTruncation`), source chapter `BookProof/ChapterChapterSirkTruncation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTruncation.lean

-- Generated from ChapterSirkTruncation.lean — theorem BookProof.ChapterSirkTruncation.adjoint_reconstruction_eq
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

theorem BookProof.ChapterSirkTruncation.adjoint_reconstruction_eq (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (v : E) :
    V.adjoint (V (V.adjoint v)) = V.adjoint v := by sorry
