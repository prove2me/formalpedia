-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTruncation_sirk_end_to_end_truncated
-- name    : BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:55:50.943149+00:00
-- url     : https://prove2.me/theorems/77c388c7-ee2e-4619-b10b-e3f0783769c3
-- title:
--   (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F) (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F) (C Dmin h : ℝ) (m : ℕ) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated` (module `BookProof.ChapterSirkTruncation`), source chapter `BookProof/ChapterChapterSirkTruncation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTruncation.lean

-- Generated from ChapterSirkTruncation.lean — theorem BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated
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

theorem BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated
    (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F)
    (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F) (C Dmin h : ℝ) (m : ℕ)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - rX‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - rB‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hexact : rX (V (V.adjoint v)) = V (rB (V.adjoint (V (V.adjoint v)))))
    (hproj : V.adjoint (V (V.adjoint v)) = V.adjoint v) :
    ‖flow v - sirkApprox V psiB v‖
      ≤ sirkBound C Dmin h ‖v‖ m
        + ‖rX‖ * ‖v - V (V.adjoint v)‖ := by sorry
