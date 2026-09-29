-- Prove2me | Theorems.Thm_BookProof_ChapterH4_sia_error_bound
-- name    : BookProof.ChapterH4.sia_error_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:39:28.791449+00:00
-- url     : https://prove2.me/theorems/cd7d1869-b69a-4f27-9530-58e6d812838d
-- title:
--   (V : F →L[ℂ] E) (phiA psiX pX : E →L[ℂ] E) (psiB pB : F →L[ℂ] F) (C Dsia : ℝ) (hphi : phiA = psiX) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (hrt : ∀ v : E, pX v = V...
-- statement:
--   Lean 4 theorem `BookProof.ChapterH4.sia_error_bound` (module `BookProof.ChapterH4`), source chapter `BookProof/ChapterChapterH4.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH4.lean

-- Generated from ChapterH4.lean — theorem BookProof.ChapterH4.sia_error_bound
import Mathlib
import Definitions.Def_ChapterH4
open BookProof.ChapterH4









open scoped BigOperators


noncomputable section





variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH4.sia_error_bound
    (V : F →L[ℂ] E) (phiA psiX pX : E →L[ℂ] E) (psiB pB : F →L[ℂ] F)
    (C Dsia : ℝ)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, pX v = V (pB (V.adjoint v)))
    (hcx1 : ‖psiX - pX‖ ≤ C * Dsia)
    (hcx2 : ‖psiB - pB‖ ≤ C * Dsia)
    (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 2 * C * Dsia * ‖v‖ := by sorry
