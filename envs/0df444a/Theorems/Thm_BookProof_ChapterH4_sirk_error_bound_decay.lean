-- Prove2me | Theorems.Thm_BookProof_ChapterH4_sirk_error_bound_decay
-- name    : BookProof.ChapterH4.sirk_error_bound_decay
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:53:26.914577+00:00
-- url     : https://prove2.me/theorems/2f441ac8-c210-4b24-abb3-6f15ab953659
-- title:
--   (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F) (C D Dmin h m : ℝ) (hphi : phiA = psiX) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint...
-- statement:
--   Lean 4 theorem `BookProof.ChapterH4.sirk_error_bound_decay` (module `BookProof.ChapterH4`), source chapter `BookProof/ChapterChapterH4.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH4.lean

-- Generated from ChapterH4.lean — theorem BookProof.ChapterH4.sirk_error_bound_decay
import Mathlib
import Definitions.Def_ChapterH4
open BookProof.ChapterH4









open scoped BigOperators


noncomputable section





variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH4.sirk_error_bound_decay
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    (C D Dmin h m : ℝ)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, rX v = V (rB (V.adjoint v)))
    (hcx1 : ‖psiX - rX‖ ≤ C * D)
    (hcx2 : ‖psiB - rB‖ ≤ C * D)
    (hC : 0 ≤ C) (hdecay : D ≤ Real.exp (-(h * m)) * Dmin)
    (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 2 * C * Real.exp (-(h * m)) * Dmin * ‖v‖ := by sorry
