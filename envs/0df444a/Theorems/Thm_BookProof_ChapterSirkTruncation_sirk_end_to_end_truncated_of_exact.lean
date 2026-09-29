-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTruncation_sirk_end_to_end_truncated_of_exact
-- name    : BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated_of_exact
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:01:34.947755+00:00
-- url     : https://prove2.me/theorems/a8ab42e4-1f7b-492e-9bf5-dd159d71aa51
-- title:
--   (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F) (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F) (C Dmin h : ℝ) (m : ℕ) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated_of_exact` (module `BookProof.ChapterSirkTruncation`), source chapter `BookProof/ChapterChapterSirkTruncation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTruncation.lean

-- Generated from ChapterSirkTruncation.lean — theorem BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated_of_exact
import Mathlib
import Definitions.Def_ChapterSirkTruncation
open BookProof.ChapterSirkTruncation








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkWhitening
open BookProof.ChapterSirkEndToEnd
open BookProof.ChapterH6

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated_of_exact
    (V : F →L[ℂ] E) (rX : E →L[ℂ] E) (rB : F →L[ℂ] F)
    (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F) (C Dmin h : ℝ) (m : ℕ)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - rX‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - rB‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v)
    (hexact : rX (V (V.adjoint v)) = V (rB (V.adjoint (V (V.adjoint v)))))
    (hproj : V.adjoint (V (V.adjoint v)) = V.adjoint v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
