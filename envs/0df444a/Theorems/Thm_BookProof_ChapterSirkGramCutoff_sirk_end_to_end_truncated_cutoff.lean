-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_sirk_end_to_end_truncated_cutoff
-- name    : BookProof.ChapterSirkGramCutoff.sirk_end_to_end_truncated_cutoff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:13:58.519608+00:00
-- url     : https://prove2.me/theorems/1dbfe11e-4037-4776-82f7-69c28f1f8574
-- title:
--   (heig : IsGramEigen w u lam) {tol : ℝ} (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol) {d : ℕ} (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E) (rX : E →L[ℂ] E) (rB :...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.sirk_end_to_end_truncated_cutoff` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.sirk_end_to_end_truncated_cutoff
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap
open BookProof.ChapterSirkEndToEnd
open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

theorem BookProof.ChapterSirkGramCutoff.sirk_end_to_end_truncated_cutoff (heig : IsGramEigen w u lam) {tol : ℝ}
    (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol)
    {d : ℕ} (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E)
    (rX : E →L[ℂ] E) (rB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (flow psiX : E →L[ℂ] E) (psiB : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (C Dmin hrate : ℝ) (k : ℕ)
    (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)))
    (hmem : ∀ j ∈ R, ∃ z, V z = synthesis w (u j))
    (hViso : ∀ x : EuclideanSpace ℂ (Fin d), ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖adjoint V v‖ ≤ ‖v‖)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - rX‖ ≤ C * (Real.exp (-(hrate * k)) * Dmin))
    (hcx2 : ‖psiB - rB‖ ≤ C * (Real.exp (-(hrate * k)) * Dmin))
    (c : EuclideanSpace ℂ (Fin m))
    (hexact : rX (V (adjoint V (synthesis w c)))
      = V (rB (adjoint V (V (adjoint V (synthesis w c))))))
    (hproj : adjoint V (V (adjoint V (synthesis w c))) = adjoint V (synthesis w c)) :
    ‖flow (synthesis w c)
        - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB (synthesis w c)‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hrate ‖synthesis w c‖ k
        + ‖rX‖ * (Real.sqrt tol * (Real.sqrt m * ‖c‖)) := by sorry
