-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_defect_le_sqrt_cutoff
-- name    : BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:17.426845+00:00
-- url     : https://prove2.me/theorems/6a6e4062-443f-4d11-a745-b433f9b255dd
-- title:
--   (heig : IsGramEigen w u lam) {tol : ℝ} (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol) {d : ℕ} (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E) (hV : (adjoint V).comp V =...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

theorem BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff (heig : IsGramEigen w u lam) {tol : ℝ}
    (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol)
    {d : ℕ} (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E)
    (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)))
    (hmem : ∀ k ∈ R, ∃ z, V z = synthesis w (u k)) (i : Fin m) :
    ‖w i - V (adjoint V (w i))‖ ≤ Real.sqrt tol := by sorry
