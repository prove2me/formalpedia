-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_sirk_end_to_end_truncated_gram
-- name    : BookProof.ChapterSirkGramWhitening.sirk_end_to_end_truncated_gram
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:02:48.506206+00:00
-- url     : https://prove2.me/theorems/62876f33-4c29-4f41-8d15-a4100601f8c1
-- title:
--   {m d : ℕ} (w : Fin m → E) (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E) (rX : E →L[ℂ] E) (rB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) (flow psiX : E →L[ℂ] E)...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.sirk_end_to_end_truncated_gram` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.sirk_end_to_end_truncated_gram
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.sirk_end_to_end_truncated_gram {m d : ℕ} (w : Fin m → E)
    (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E)
    (rX : E →L[ℂ] E) (rB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (flow psiX : E →L[ℂ] E) (psiB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (C Dmin hrate : ℝ) (k : ℕ) {delta : ℝ}
    (hViso : ∀ x : EuclideanSpace ℂ (Fin d), ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖ContinuousLinearMap.adjoint V v‖ ≤ ‖v‖)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - rX‖ ≤ C * (Real.exp (-(hrate * k)) * Dmin))
    (hcx2 : ‖psiB - rB‖ ≤ C * (Real.exp (-(hrate * k)) * Dmin))
    (hdelta : ∀ i, ‖w i - V (ContinuousLinearMap.adjoint V (w i))‖ ≤ delta)
    (c : EuclideanSpace ℂ (Fin m))
    (hexact : rX (V (ContinuousLinearMap.adjoint V (synthesis w c)))
      = V (rB (ContinuousLinearMap.adjoint V
        (V (ContinuousLinearMap.adjoint V (synthesis w c))))))
    (hproj : ContinuousLinearMap.adjoint V (V (ContinuousLinearMap.adjoint V (synthesis w c)))
      = ContinuousLinearMap.adjoint V (synthesis w c)) :
    ‖flow (synthesis w c)
        - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB (synthesis w c)‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hrate ‖synthesis w c‖ k
        + ‖rX‖ * (delta * (Real.sqrt m * ‖c‖)) := by sorry
