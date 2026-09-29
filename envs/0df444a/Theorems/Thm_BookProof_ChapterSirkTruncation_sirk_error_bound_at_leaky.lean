-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTruncation_sirk_error_bound_at_leaky
-- name    : BookProof.ChapterSirkTruncation.sirk_error_bound_at_leaky
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:12.08543+00:00
-- url     : https://prove2.me/theorems/64db1496-1acb-406e-8857-ace6c757e838
-- title:
--   (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F) (C D rho : ℝ) (hphi : phiA = psiX) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (hcx1 : ‖psiX - rX‖ ≤ C *...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTruncation.sirk_error_bound_at_leaky` (module `BookProof.ChapterSirkTruncation`), source chapter `BookProof/ChapterChapterSirkTruncation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTruncation.lean

-- Generated from ChapterSirkTruncation.lean — theorem BookProof.ChapterSirkTruncation.sirk_error_bound_at_leaky
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

theorem BookProof.ChapterSirkTruncation.sirk_error_bound_at_leaky
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    (C D rho : ℝ)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hcx1 : ‖psiX - rX‖ ≤ C * D)
    (hcx2 : ‖psiB - rB‖ ≤ C * D)
    (v : E) (hrt : ‖rX v - V (rB (V.adjoint v))‖ ≤ rho) :
    ‖phiA v - sirkApprox V psiB v‖ ≤ 2 * C * D * ‖v‖ + rho := by sorry
