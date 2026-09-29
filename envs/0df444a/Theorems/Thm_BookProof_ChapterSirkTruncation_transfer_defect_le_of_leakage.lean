-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTruncation_transfer_defect_le_of_leakage
-- name    : BookProof.ChapterSirkTruncation.transfer_defect_le_of_leakage
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:25.915621+00:00
-- url     : https://prove2.me/theorems/5cd16d10-c985-4aba-a899-c5305660d054
-- title:
--   (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F) (v : E) (hexact : rX (V (V.adjoint v)) = V (rB (V.adjoint (V (V.adjoint v))))) (hproj : V.adjoint (V (V.adjoint v)) = V.adjoint v) : ‖rX v - V...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTruncation.transfer_defect_le_of_leakage` (module `BookProof.ChapterSirkTruncation`), source chapter `BookProof/ChapterChapterSirkTruncation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTruncation.lean

-- Generated from ChapterSirkTruncation.lean — theorem BookProof.ChapterSirkTruncation.transfer_defect_le_of_leakage
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

theorem BookProof.ChapterSirkTruncation.transfer_defect_le_of_leakage (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F)
    (v : E) (hexact : rX (V (V.adjoint v)) = V (rB (V.adjoint (V (V.adjoint v)))))
    (hproj : V.adjoint (V (V.adjoint v)) = V.adjoint v) :
    ‖rX v - V (rB (V.adjoint v))‖ ≤ ‖rX‖ * ‖v - V (V.adjoint v)‖ := by sorry
