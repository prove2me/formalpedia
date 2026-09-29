-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirk_end_to_end
-- name    : BookProof.ChapterSirkEndToEnd.sirk_end_to_end
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:46:30.894487+00:00
-- url     : https://prove2.me/theorems/cf7173c8-2e66-46d3-8a9f-86941da52f75
-- title:
--   (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F) (p : Polynomial ℂ) (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F) (C Dmin h : ℝ) (m : ℕ) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.sirk_end_to_end` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.sirk_end_to_end
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.sirk_end_to_end
    (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F) (p : Polynomial ℂ)
    (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F)
    (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (hinvq : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - (Polynomial.aeval X p).comp qXinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - (Polynomial.aeval (compress V X) p).comp qBinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
